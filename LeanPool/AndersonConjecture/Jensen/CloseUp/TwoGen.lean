/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.CloseUp.Base
import LeanPool.AndersonConjecture.Jensen.KrullDomain.KrullDomain

/-!
# Close-up: two-generator ideals

The crux case of Heitmann's Lemma 4: given an A-extension R of
a Noetherian local domain T and an ideal I = (a, b) with a
nonzero element c in the span, produce a new A-extension in
which the close-up condition holds for I. The coprime case is
handled directly
the general case reduces to it by extracting
common factors.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Crux case: two generators (n = 2)

If I = (y₁, y₂)R and c ∈ IT ∩ R, write c = t₁y₁ + t₂y₂.
Parameterize: c = (t₁ + ty₂)y₁ + (t₂ - ty₁)y₂.
Choose t via avoidance, set x₁ = t₁ + ty₂, x₂ = t₂ - ty₁.
The ring Rbar = R[x₁, y₂⁻¹] ∩ R[x₂, y₁⁻¹] localized at M is an A-extension
with c = x₁y₁ + x₂y₂ ∈ IRbar.

## Proof strategy (single adjoin + generalized close_up)
1. Decompose c = t₁·y₁ + t₂·y₂ in T (from Submodule.mem_span_pair)
2. Choose t via countable_avoidance so x₁ = t₁ + t·y₂ is transcendental
   over R and avoids associated primes of T/rT for all nonzero r ∈ R
3. Adjoin x₁ to R via adjoin_transcendental_isNSubring → get S with x₁ ∈ S
4. In S: c - x₁·y₁ = (t₂ - t·y₁)·y₂ ∈ y₂·T, and c - x₁·y₁ ∈ S
5. By close_up_dvd on S: c - x₁·y₁ ∈ y₂·S, i.e.,
   ∃ x₂' ∈ S, c - x₁·y₁ = x₂'·y₂
6. Then c = x₁·y₁ + x₂'·y₂ ∈ span{y₁, y₂} in S
-/

/-- Coprime case of two-generator close-up: when y₁, y₂ have no common
prime factor in R, find A-extension S with c - x₁·y₁ ∈ span{y₂} in S.
This is the hard case requiring Krull domain intersection machinery. -/
theorem close_up_two_gen_coprime
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T) (y₁ y₂ : R.carrier) (c : R.carrier)
    (hc : (c : T) ∈ Ideal.span {(y₁ : T), (y₂ : T)})
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    ∃ S : NSubring T, IsAExtension R S ∧
      ∃ (hle : R.carrier ≤ S.carrier) (x₁ : S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) - x₁ * ⟨(y₁ : T), hle y₁.2⟩ ∈
          Ideal.span {⟨(y₂ : T), hle y₂.2⟩} := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  /- Strategy (Heitmann Lemma 4, coprime case — Krull domain intersection):
     Handle degenerate cases first (y₂=0, M=⊥, y₁=0), then delegate to
     intersection_close_up from KrullDomain.lean for the main case. -/
  by_cases hy₂_zero : (↑y₂ : T) = 0
  · have hc' : (c : T) ∈ Ideal.span {(y₁ : T)} := by
      apply Ideal.span_le.mpr _ hc
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact Ideal.subset_span rfl
      · rw [Set.mem_singleton_iff.mp hx, hy₂_zero]
        exact Ideal.zero_mem _
    obtain ⟨c', hcc'⟩ := Ideal.mem_span_singleton.mp (close_up_dvd R y₁ c hc')
    refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, c', ?_⟩
    have heq : c - c' * y₁ = 0 := by rw [hcc', mul_comm, sub_self]
    change c - c' * y₁ ∈ Ideal.span {y₂}
    rw [heq]
    exact Ideal.zero_mem _
  have hy₂_ne : (↑y₂ : T) ≠ 0 := hy₂_zero
  by_cases hM_bot : IsLocalRing.maximalIdeal T = ⊥
  · have hR_field : IsLocalRing.maximalIdeal R.carrier = ⊥ := by
      rw [R.maximal_ideal_eq, hM_bot, Ideal.comap_bot_of_injective _ Subtype.val_injective]
    have hy₂_unit : IsUnit y₂ := by
      by_contra h
      have hmem : y₂ ∈ IsLocalRing.maximalIdeal R.carrier :=
        (IsLocalRing.mem_maximalIdeal _).mpr h
      rw [hR_field, Ideal.mem_bot] at hmem
      exact hy₂_ne (congr_arg Subtype.val hmem)
    refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, 0, ?_⟩
    change c - 0 * y₁ ∈ Ideal.span {y₂}
    simp only [zero_mul, sub_zero]
    have : Ideal.span {y₂} = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span rfl) hy₂_unit
    rw [this]
    exact Submodule.mem_top
  by_cases hy₁_zero : (↑y₁ : T) = 0
  · have hc_span_y₂ : (c : T) ∈ Ideal.span {(y₂ : T)} := by
      apply Ideal.span_le.mpr _ hc
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · rw [hy₁_zero]
        exact Ideal.zero_mem _
      · exact Ideal.subset_span (Set.mem_singleton_iff.mp hx ▸ rfl)
    have := close_up_dvd R y₂ c hc_span_y₂
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp this
    refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, 0, ?_⟩
    change c - 0 * y₁ ∈ Ideal.span {y₂}
    simpa only [zero_mul, sub_zero] using Ideal.mem_span_singleton.mpr ⟨q, hq⟩
  exact intersection_close_up R y₁ y₂ c hc hcoprime hy₁_zero hy₂_zero hM_bot
    hM_not_assoc hAss_ht hR_card hT_card

/-- Key construction for the common factor case of close_up_two_gen:
Given y₁ = p*a, y₂ = p*b with p prime and c ∈ span{y₁,y₂}T,
factor out p using close_up_dvd, cancel it, and reduce to (a,b).
Uses WF induction on y₁ via DvdNotUnit to handle the recursive case. -/
theorem close_up_two_gen_key
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (y₁ y₂ : R.carrier)
    (c : R.carrier)
    (hc : (c : T) ∈ Ideal.span {(y₁ : T), (y₂ : T)})
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    ∃ S : NSubring T, IsAExtension R S ∧
      ∃ (hle : R.carrier ≤ S.carrier) (x₁ : S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) - x₁ * ⟨(y₁ : T), hle y₁.2⟩ ∈
          Ideal.span {⟨(y₂ : T), hle y₂.2⟩} := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  revert y₂ c hc
  apply wellFounded_dvdNotUnit.induction y₁
  intro y₁ ih y₂ c hc
  by_cases hcop : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂)
  · exact close_up_two_gen_coprime R y₁ y₂ c hc hcop
      hM_not_assoc hAss_ht hR_card hT_card
  · push Not at hcop
    obtain ⟨p, hp, hpy1, hpy2⟩ := hcop
    obtain ⟨a, rfl⟩ := hpy1
    obtain ⟨b, rfl⟩ := hpy2
    have hpa : ((p * a : R.carrier) : T) = (p : T) * (a : T) :=
      map_mul R.carrier.subtype p a
    have hpb : ((p * b : R.carrier) : T) = (p : T) * (b : T) :=
      map_mul R.carrier.subtype p b
    have hc_p : (c : T) ∈ Ideal.span {(p : T)} :=
      (Ideal.span_le.mpr fun x hx => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · rw [hpa]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
        · rw [hpb]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) hc
    have hc_pR := close_up_dvd R p c hc_p
    rw [Ideal.mem_span_singleton] at hc_pR
    obtain ⟨c', hcc'⟩ := hc_pR
    have hp_ne : (p : T) ≠ 0 := fun h => hp.ne_zero (Subtype.val_injective h)
    have hpc : (c : T) = (p : T) * (c' : T) := by
      have := congr_arg Subtype.val hcc'
      simp only [Subring.coe_mul] at this
      exact this
    have hc'_ab : (c' : T) ∈ Ideal.span {(a : T), (b : T)} := by
      obtain ⟨u₁, u₂, hu⟩ := Submodule.mem_span_pair.mp hc
      rw [hpa, hpb, smul_eq_mul, smul_eq_mul] at hu
      have heq : (p : T) * (c' : T) = (p : T) * (u₁ * (a : T) + u₂ * (b : T)) := by
        rw [← hpc, ← hu]
        ring
      exact Submodule.mem_span_pair.mpr ⟨u₁, u₂, by
        rw [smul_eq_mul, smul_eq_mul]
        exact (mul_left_cancel₀ hp_ne heq).symm⟩
    by_cases ha : a = 0
    · subst ha
      have hc'_b : (c' : T) ∈ Ideal.span {(b : T)} :=
        (Ideal.span_le.mpr (fun x hx => by
          rcases Set.mem_insert_iff.mp hx with rfl | h
          · change (0 : T) ∈ _
            exact Submodule.zero_mem _
          · exact Ideal.subset_span h)) hc'_ab
      have hc'R := close_up_dvd R b c' hc'_b
      refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, 0, ?_⟩
      simp only [zero_mul, sub_zero]
      rw [Ideal.mem_span_singleton] at hc'R ⊢
      obtain ⟨q, hq⟩ := hc'R
      refine ⟨⟨(q : T), q.2⟩, Subtype.ext ?_⟩
      have hc'_val : (c' : T) = (b : T) * (q : T) := by
        have := congr_arg Subtype.val hq
        simp only [Subring.coe_mul] at this
        exact this
      simp only [Subring.coe_mul]
      rw [hpc, hc'_val, mul_assoc]
    · have hdvd : DvdNotUnit a (p * a) := ⟨ha, ⟨p, hp.not_unit, mul_comm p a⟩⟩
      obtain ⟨S, hAext, hle, x₁, hrem⟩ := ih a hdvd b c' hc'_ab
      refine ⟨S, hAext, hle, x₁, ?_⟩
      have hpa_S : (⟨((p * a : R.carrier) : T), hle (p * a).2⟩ : S.carrier) =
          ⟨(p : T), hle p.2⟩ * ⟨(a : T), hle a.2⟩ :=
        Subtype.ext (map_mul R.carrier.subtype p a)
      have hpb_S : (⟨((p * b : R.carrier) : T), hle (p * b).2⟩ : S.carrier) =
          ⟨(p : T), hle p.2⟩ * ⟨(b : T), hle b.2⟩ :=
        Subtype.ext (map_mul R.carrier.subtype p b)
      have hc_S : (⟨(c : T), hle c.2⟩ : S.carrier) =
          ⟨(p : T), hle p.2⟩ * ⟨(c' : T), hle c'.2⟩ :=
        Subtype.ext hpc
      rw [hc_S, hpa_S, hpb_S]
      have hrearr : x₁ * (⟨(p : T), hle p.2⟩ * ⟨(a : T), hle a.2⟩) =
          ⟨(p : T), hle p.2⟩ * (x₁ * ⟨(a : T), hle a.2⟩) := by
        rw [← mul_assoc, mul_comm x₁, mul_assoc]
      rw [hrearr, ← mul_sub]
      rw [Ideal.mem_span_singleton] at hrem ⊢
      obtain ⟨q, hq⟩ := hrem
      exact ⟨q, by rw [hq, mul_assoc]⟩

/-- Close-up for two-generator ideals: if I = (y₁, y₂) and c ∈ IT ∩ R,
there exists an A-extension S with c ∈ IS. This is the crux of Lemma 4. -/
theorem close_up_two_gen
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (y₁ y₂ : R.carrier)
    (c : R.carrier)
    (hc : (c : T) ∈ (Ideal.span {(y₁ : T), (y₂ : T)}))
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.span {⟨(y₁ : T), hle y₁.2⟩, ⟨(y₂ : T), hle y₂.2⟩} := by
  obtain ⟨t₁, t₂, hc_eq⟩ := Submodule.mem_span_pair.mp hc
  -- Reduce to finding x₁ ∈ S with c - x₁·y₁ ∈ span{y₂}
  suffices key : ∃ S : NSubring T, IsAExtension R S ∧
      ∃ (hle : R.carrier ≤ S.carrier) (x₁ : S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) - x₁ * ⟨(y₁ : T), hle y₁.2⟩ ∈
          Ideal.span {⟨(y₂ : T), hle y₂.2⟩} by
    obtain ⟨S, hAext, hle, x₁, hrem⟩ := key
    refine ⟨S, hAext, hle, ?_⟩
    rw [Ideal.mem_span_singleton] at hrem
    obtain ⟨x₂, hx₂⟩ := hrem
    set y₁_S := (⟨(y₁ : T), hle y₁.2⟩ : S.carrier)
    set y₂_S := (⟨(y₂ : T), hle y₂.2⟩ : S.carrier)
    have hc_eq : (⟨(c : T), hle c.2⟩ : S.carrier) = x₁ * y₁_S + x₂ * y₂_S := by
      linear_combination hx₂
    rw [hc_eq]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ x₁ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ x₂ (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))))
  exact close_up_two_gen_key R y₁ y₂ c hc
    hM_not_assoc hAss_ht hR_card hT_card

/-!
## General case: n generators (induction)

For n > 2, reduce to the n-1 case by factoring out common prime factors
and applying the two-generator case.
-/

/-- Local copy of isAExtension_trans (CombinedStep.lean has circular import). -/
theorem isAExtension_trans' {R S U : NSubring T}
    (h₁ : IsAExtension R S) (h₂ : IsAExtension S U) : IsAExtension R U where
  le := le_trans h₁.le h₂.le
  primes_preserved r hr :=
    h₂.primes_preserved ⟨r.1, h₁.le r.2⟩ (h₁.primes_preserved r hr)
  card_le := by
    calc Cardinal.mk U.carrier
        ≤ max Cardinal.aleph0 (Cardinal.mk S.carrier) := h₂.card_le
      _ ≤ max Cardinal.aleph0 (max Cardinal.aleph0 (Cardinal.mk R.carrier)) :=
          max_le_max_left _ h₁.card_le
      _ = max Cardinal.aleph0 (Cardinal.mk R.carrier) := by
          rw [← max_assoc, max_self]

lemma exists_prime_mem_of_ne_bot_closeup {S : Type*} [CommRing S] [IsDomain S]
    [UniqueFactorizationMonoid S]
    (Q : Ideal S) [hQ : Q.IsPrime] (hQ_ne_bot : Q ≠ ⊥) :
    ∃ q : S, Prime q ∧ q ∈ Q := by
  obtain ⟨a, haQ, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ_ne_bot
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
  · have hb_ne : b ≠ 0 := right_ne_zero_of_mul (hxpb ▸ hx_ne)
    have hb_nu : ¬IsUnit b := fun hu => hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hb_Q hu)
    exact ih b ⟨hb_ne, p, hp_irr.prime.not_unit, by rw [hxpb, mul_comm]⟩ hb_ne hb_nu hb_Q

end
