/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Avoidance
import LeanPool.AndersonConjecture.Jensen.KrullDomain.HeightBound
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Krull Domain Intersection for Two-Generator Close-Up

Given coprime y₁, y₂ in an N-subring R and c ∈ (y₁,y₂)T ∩ R,
construct an A-extension S with c ∈ (y₁,y₂)S via the intersection
Rbar = R[x₁, y₂⁻¹] ∩ R[x₂, y₁⁻¹] where c = x₁y₁ + x₂y₂.
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

section MainTheorem

variable [IsAdicComplete (IsLocalRing.maximalIdeal T) T]

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/- Shared height-1 step for the kernel proofs: a height-≤-1 prime `P` of `T`
containing a prime `p` of `R` is an associated prime of `T/(p)`, and `(p)R`
equals `P ∩ R`. -/
include T in private theorem ker_pf_span_eq
    (R : NSubring T) (P : Ideal T) (hP_prime : P.IsPrime) (hP_ht : P.height ≤ 1)
    (p : R.carrier) (hp : Prime p) (hp_P : (↑p : T) ∈ P)
    (hp_ne : (↑p : T) ≠ 0) :
    P ∈ associatedPrimes T (T ⧸ Ideal.span {(↑p : T)}) ∧
      Ideal.span {p} = P.comap R.carrier.subtype := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  have hP_minimal : P ∈ (Ideal.span {(↑p : T)}).minimalPrimes := by
    refine ⟨⟨hP_prime, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp_P)⟩, ?_⟩
    intro Q ⟨hQ_prime, hQ_le⟩ hQ_le_P
    by_contra hne
    have hQ_strict : Q < P :=
      lt_of_le_of_ne hQ_le_P (fun h => hne (h ▸ le_refl P))
    have hp_Q : (↑p : T) ∈ Q := hQ_le (Ideal.mem_span_singleton_self _)
    have hQ_ne_bot : Q ≠ ⊥ := by
      intro h
      rw [h] at hp_Q
      exact hp_ne (Ideal.mem_bot.mp hp_Q)
    have hQ_ht_le : Q.height ≤ 1 := le_trans (Ideal.height_mono hQ_le_P) hP_ht
    have hQ_fin : Q.FiniteHeight := ⟨Or.inr (by
      exact ne_top_of_le_ne_top (by norm_cast) hQ_ht_le)⟩
    have hQ_ht_lt := @Ideal.height_strict_mono_of_isPrime T _ Q P hQ_prime hQ_strict hQ_fin
    have hbot_lt : (⊥ : Ideal T) < Q := bot_lt_iff_ne_bot.mpr hQ_ne_bot
    have hbot_fin : (⊥ : Ideal T).FiniteHeight :=
      ⟨Or.inr (by simp [Ideal.height_bot])⟩
    have h0 := @Ideal.height_strict_mono_of_isPrime T _
      (⊥ : Ideal T) Q Ideal.isPrime_bot hbot_lt hbot_fin
    rw [Ideal.height_bot] at h0
    exact absurd h0 (not_lt.mpr (le_of_eq
      (Order.lt_one_iff.mp (lt_of_lt_of_le hQ_ht_lt hP_ht))))
  have hP_ass : P ∈ associatedPrimes T (T ⧸ Ideal.span {(↑p : T)}) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rwa [Ideal.annihilator_quotient]
  have hht := R.height_bound (↑p : T) hp_ne P hP_ass
  haveI : P.IsPrime := hP_prime
  haveI : (P.comap R.carrier.subtype).IsPrime := Ideal.comap_isPrime _ _
  have hspan_le : Ideal.span {p} ≤ P.comap R.carrier.subtype :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (show (↑p : T) ∈ P from hp_P))
  have hspan_ne : Ideal.span {p} ≠ (⊥ : Ideal R.carrier) :=
    Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  haveI : (Ideal.span {p}).IsPrime :=
    (Ideal.span_singleton_prime (α := R.carrier) hp.ne_zero).mpr hp
  refine ⟨hP_ass, ?_⟩
  by_contra hne
  have hstrict := lt_of_le_of_ne hspan_le hne
  rw [show (1 : ℕ∞) = ↑(1 : ℕ) from rfl] at hht
  rw [Ideal.height_le_iff] at hht
  have hspan_ht := hht (Ideal.span {p}) inferInstance hstrict
  have hbot_lt := bot_lt_iff_ne_bot.mpr hspan_ne
  have hbot_fin : (⊥ : Ideal R.carrier).FiniteHeight :=
    ⟨Or.inr (by simp [Ideal.height_bot])⟩
  have h0 := @Ideal.height_strict_mono_of_isPrime R.carrier _
    (⊥ : Ideal R.carrier) (Ideal.span {p}) Ideal.isPrime_bot hbot_lt hbot_fin
  rw [Ideal.height_bot] at h0
  rw [show (↑(1 : ℕ) : ℕ∞) = 1 from rfl, Order.lt_one_iff] at hspan_ht
  rw [hspan_ht] at h0
  exact lt_irrefl _ h0

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/-- Helper for `intersection_close_up`: kernel proof for x₁ = t₁ + u·y₂.
    Shows that for each height-≤-1 prime P with y₂ ∉ P and p ∈ P prime in R,
    any polynomial f with aeval(x₁) f ∈ P is divisible by C(p). -/
private def intersection_close_up_proof_ker_pf₁
    (R : NSubring T) (y₂ : R.carrier) (t₁ u : T)
    (C_ext : Set (Ideal T))
    (D_ext : Set T)
    (hC_ext_mem : ∀ (p : R.carrier), (↑p : T) ≠ 0 →
        ∀ P, P ∈ associatedPrimes T (T ⧸ Ideal.span {(↑p : T)}) → P ∈ C_ext)
    (hD_ext_invFun : ∀ (f : Polynomial R.carrier), f ≠ 0 →
        ∀ (P : Ideal T), P ∈ C_ext → P ≠ ⊥ →
        Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0 →
        Ideal.Quotient.mk P (↑y₂ : T) ≠ 0 →
        ∀ v₀, v₀ ∈ {v : T ⧸ P |
          (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
            (Ideal.Quotient.mk P t₁ + v * Ideal.Quotient.mk P (↑y₂ : T)) = 0} →
        Function.invFun (Ideal.Quotient.mk P) v₀ ∈ D_ext)
    (hu_avoid : ∀ P ∈ C_ext, ∀ r ∈ D_ext,
        u ∉ (P : Set T) + ({r} : Set T))
    (P : Ideal T) (hP_prime : P.IsPrime) (_hP_ne_top : P ≠ ⊤) (hP_ht : P.height ≤ 1)
    (hy₂_nP : (↑y₂ : T) ∉ P)
    (p : R.carrier) (hp : Prime p) (hp_P : (↑p : T) ∈ P)
    (f : Polynomial R.carrier)
    (hf_mem : aeval (t₁ + u * (↑y₂ : T)) f ∈ P) : PLift (
    (Polynomial.C p : Polynomial R.carrier) ∣ f ) := ⟨by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  by_contra h_ndvd
  have hp_ne : (↑p : T) ≠ 0 := fun h => hp.ne_zero (R.carrier.subtype_injective h)
  have hP_ne_bot : P ≠ ⊥ := by
    intro h
    rw [h] at hp_P
    exact hp_ne (Ideal.mem_bot.mp hp_P)
  obtain ⟨hP_ass, hspan_eq⟩ := ker_pf_span_eq R P hP_prime hP_ht p hp hp_P hp_ne
  have hP_C : P ∈ C_ext := hC_ext_mem p hp_ne P hP_ass
  -- fbar ≠ 0 in (T/P)[X]: if fbar = 0 then all coefficients lie in P ∩ R = (p), so p | f
  have hmap_ne : Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0 := by
    intro h_eq
    apply h_ndvd
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    have h_coeff : Polynomial.coeff
        (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f) n = 0 := by
      rw [h_eq]
      exact Polynomial.coeff_zero n
    rw [Polynomial.coeff_map] at h_coeff
    have h_in_P : (↑(f.coeff n) : T) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact h_coeff
    have h_in_comap : f.coeff n ∈ P.comap R.carrier.subtype := h_in_P
    rw [← hspan_eq] at h_in_comap
    exact Ideal.mem_span_singleton.mp h_in_comap
  have hy₂_ne_P : Ideal.Quotient.mk P (↑y₂ : T) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hy₂_nP
  -- Push f(x₁) ∈ P to fbar(tbar₁ + ū·ybar₂) = 0 in T/P via the quotient map
  have heval_P : aeval (t₁ + u * (↑y₂ : T)) f ∈ P := hf_mem
  have heval_zero : (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
      (Ideal.Quotient.mk P t₁ + Ideal.Quotient.mk P u *
        Ideal.Quotient.mk P (↑y₂ : T)) = 0 := by
    have h1 : Ideal.Quotient.mk P (aeval (t₁ + u * (↑y₂ : T)) f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr heval_P
    rw [Polynomial.aeval_def,
      show algebraMap R.carrier T = R.carrier.subtype from rfl,
      Polynomial.hom_eval₂ f R.carrier.subtype (Ideal.Quotient.mk P)
        (t₁ + u * (↑y₂ : T)),
      ← Polynomial.eval_map] at h1
    rwa [map_add, map_mul] at h1
  -- Lift ū mod P to r₀ ∈ T; then ū is a root of fbar so r₀ ∈ D_ext
  set v₀ := Ideal.Quotient.mk P u
  set r₀ := Function.invFun (Ideal.Quotient.mk P) v₀
  have hP_surj : Function.Surjective (Ideal.Quotient.mk P) :=
    Ideal.Quotient.mk_surjective
  have hmk_r₀ : Ideal.Quotient.mk P r₀ = v₀ :=
    Function.invFun_eq (hP_surj v₀)
  have hv₀_root : v₀ ∈ {v : T ⧸ P |
      (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
        (Ideal.Quotient.mk P t₁ + v * Ideal.Quotient.mk P (↑y₂ : T)) = 0} := by
    simpa only [Set.mem_setOf_eq] using heval_zero
  have hf_ne : f ≠ 0 := by
    intro h
    apply h_ndvd
    rw [h]
    exact dvd_zero _
  have hr₀_D : r₀ ∈ D_ext :=
    hD_ext_invFun f hf_ne P hP_C hP_ne_bot hmap_ne hy₂_ne_P v₀ hv₀_root
  -- u ≡ r₀ mod P, so u ∈ P + {r₀}, contradicting the avoidance hypothesis
  have hu_r₀_P : u - r₀ ∈ (P : Set T) := by
    change u - r₀ ∈ P
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmk_r₀]
    exact sub_self v₀
  open scoped Pointwise in
  have hu_coset : u ∈ (P : Set T) + ({r₀} : Set T) :=
    ⟨u - r₀, hu_r₀_P, r₀, rfl, by ring⟩
  exact hu_avoid P hP_C r₀ hr₀_D hu_coset
⟩

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
include T in theorem intersection_close_up_ker_pf₁
    (R : NSubring T) (y₂ : R.carrier) (t₁ u : T)
    (C_ext : Set (Ideal T))
    (D_ext : Set T)
    (hC_ext_mem : ∀ (p : R.carrier), (↑p : T) ≠ 0 →
        ∀ P, P ∈ associatedPrimes T (T ⧸ Ideal.span {(↑p : T)}) → P ∈ C_ext)
    (hD_ext_invFun : ∀ (f : Polynomial R.carrier), f ≠ 0 →
        ∀ (P : Ideal T), P ∈ C_ext → P ≠ ⊥ →
        Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0 →
        Ideal.Quotient.mk P (↑y₂ : T) ≠ 0 →
        ∀ v₀, v₀ ∈ {v : T ⧸ P |
          (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
            (Ideal.Quotient.mk P t₁ + v * Ideal.Quotient.mk P (↑y₂ : T)) = 0} →
        Function.invFun (Ideal.Quotient.mk P) v₀ ∈ D_ext)
    (hu_avoid : ∀ P ∈ C_ext, ∀ r ∈ D_ext,
        u ∉ (P : Set T) + ({r} : Set T))
    (P : Ideal T) (hP_prime : P.IsPrime) (_hP_ne_top : P ≠ ⊤) (hP_ht : P.height ≤ 1)
    (hy₂_nP : (↑y₂ : T) ∉ P)
    (p : R.carrier) (hp : Prime p) (hp_P : (↑p : T) ∈ P)
    (f : Polynomial R.carrier)
    (hf_mem : aeval (t₁ + u * (↑y₂ : T)) f ∈ P) :
    (Polynomial.C p : Polynomial R.carrier) ∣ f := by
  exact
    (intersection_close_up_proof_ker_pf₁
      R y₂ t₁ u C_ext D_ext hC_ext_mem hD_ext_invFun hu_avoid P hP_prime _hP_ne_top hP_ht
      hy₂_nP p hp hp_P f hf_mem
    ).down
omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/- Helper for `intersection_close_up`: kernel proof for x₂ = t₂ - u·y₁.
    Shows that for each height-≤-1 prime P with y₁ ∉ P and p ∈ P prime in R,
    any polynomial f with aeval(x₂) f ∈ P is divisible by C(p). -/
include T in theorem intersection_close_up_ker_pf₂
    (R : NSubring T) (y₁ : R.carrier) (t₂ u : T)
    (C_ext : Set (Ideal T))
    (D_ext : Set T)
    (hC_ext_mem : ∀ (p : R.carrier), (↑p : T) ≠ 0 →
        ∀ P, P ∈ associatedPrimes T (T ⧸ Ideal.span {(↑p : T)}) → P ∈ C_ext)
    (hD_ext_invFun : ∀ (f : Polynomial R.carrier), f ≠ 0 →
        ∀ (P : Ideal T), P ∈ C_ext → P ≠ ⊥ →
        Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0 →
        Ideal.Quotient.mk P (↑y₁ : T) ≠ 0 →
        ∀ v₀, v₀ ∈ {v : T ⧸ P |
          (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
            (Ideal.Quotient.mk P t₂ - v * Ideal.Quotient.mk P (↑y₁ : T)) = 0} →
        Function.invFun (Ideal.Quotient.mk P) v₀ ∈ D_ext)
    (hu_avoid : ∀ P ∈ C_ext, ∀ r ∈ D_ext,
        u ∉ (P : Set T) + ({r} : Set T))
    (P : Ideal T) (hP_prime : P.IsPrime) (_hP_ne_top : P ≠ ⊤) (hP_ht : P.height ≤ 1)
    (hy₁_nP : (↑y₁ : T) ∉ P)
    (p : R.carrier) (hp : Prime p) (hp_P : (↑p : T) ∈ P)
    (f : Polynomial R.carrier)
    (hf_mem : aeval (t₂ - u * (↑y₁ : T)) f ∈ P) :
    (Polynomial.C p : Polynomial R.carrier) ∣ f := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  by_contra h_ndvd
  have hp_ne : (↑p : T) ≠ 0 := fun h => hp.ne_zero (R.carrier.subtype_injective h)
  have hP_ne_bot : P ≠ ⊥ := by
    intro h
    rw [h] at hp_P
    exact hp_ne (Ideal.mem_bot.mp hp_P)
  obtain ⟨hP_ass, hspan_eq⟩ := ker_pf_span_eq R P hP_prime hP_ht p hp hp_P hp_ne
  have hP_C : P ∈ C_ext := hC_ext_mem p hp_ne P hP_ass
  -- fbar ≠ 0 mod P since p ∤ f and (p)R = P ∩ R
  have hmap_ne : Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0 := by
    intro h_eq
    apply h_ndvd
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    have h_coeff : Polynomial.coeff
        (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f) n = 0 := by
      rw [h_eq]
      exact Polynomial.coeff_zero n
    rw [Polynomial.coeff_map] at h_coeff
    have h_in_P : (↑(f.coeff n) : T) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact h_coeff
    have h_in_comap : f.coeff n ∈ P.comap R.carrier.subtype := h_in_P
    rw [← hspan_eq] at h_in_comap
    exact Ideal.mem_span_singleton.mp h_in_comap
  have hy₁_ne_P : Ideal.Quotient.mk P (↑y₁ : T) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hy₁_nP
  -- fbar(tbar₂ - ū·ybar₁) = 0 in T/P, so ū is a root of the shifted polynomial
  have heval_P : aeval (t₂ - u * (↑y₁ : T)) f ∈ P := hf_mem
  have heval_zero : (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
      (Ideal.Quotient.mk P t₂ - Ideal.Quotient.mk P u *
        Ideal.Quotient.mk P (↑y₁ : T)) = 0 := by
    have h1 : Ideal.Quotient.mk P (aeval (t₂ - u * (↑y₁ : T)) f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr heval_P
    rw [Polynomial.aeval_def,
      show algebraMap R.carrier T = R.carrier.subtype from rfl,
      Polynomial.hom_eval₂ f R.carrier.subtype (Ideal.Quotient.mk P)
        (t₂ - u * (↑y₁ : T)),
      ← Polynomial.eval_map] at h1
    rwa [map_sub, map_mul] at h1
  -- Lift ū to r₀ ∈ D_ext, then u ∈ P + {r₀} contradicts avoidance
  set v₀ := Ideal.Quotient.mk P u
  set r₀ := Function.invFun (Ideal.Quotient.mk P) v₀
  have hP_surj : Function.Surjective (Ideal.Quotient.mk P) :=
    Ideal.Quotient.mk_surjective
  have hmk_r₀ : Ideal.Quotient.mk P r₀ = v₀ :=
    Function.invFun_eq (hP_surj v₀)
  have hv₀_root : v₀ ∈ {v : T ⧸ P |
      (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
        (Ideal.Quotient.mk P t₂ - v * Ideal.Quotient.mk P (↑y₁ : T)) = 0} := by
    simpa only [Set.mem_setOf_eq] using heval_zero
  have hf_ne : f ≠ 0 := by
    intro h
    apply h_ndvd
    rw [h]
    exact dvd_zero _
  have hr₀_D : r₀ ∈ D_ext :=
    hD_ext_invFun f hf_ne P hP_C hP_ne_bot hmap_ne hy₁_ne_P v₀ hv₀_root
  have hu_r₀_P : u - r₀ ∈ (P : Set T) := by
    change u - r₀ ∈ P
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmk_r₀]
    exact sub_self v₀
  open scoped Pointwise in
  have hu_coset : u ∈ (P : Set T) + ({r₀} : Set T) :=
    ⟨u - r₀, hu_r₀_P, r₀, rfl, by ring⟩
  exact hu_avoid P hP_C r₀ hr₀_D hu_coset

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
private def intersection_close_up_proof
    (R : NSubring T) (y₁ y₂ : R.carrier) (c : R.carrier)
    (hc : (c : T) ∈ Ideal.span {(y₁ : T), (y₂ : T)})
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    PLift (∃ S : NSubring T, IsAExtension R S ∧
      ∃ (hle : R.carrier ≤ S.carrier) (x₁ : S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) - x₁ * ⟨(y₁ : T), hle y₁.2⟩ ∈
          Ideal.span {⟨(y₂ : T), hle y₂.2⟩}) := ⟨by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  -- Write c = t₁·y₁ + t₂·y₂ with t₁, t₂ ∈ T from the membership in (y₁,y₂)T
  obtain ⟨t₁, t₂, hc_eq⟩ := Submodule.mem_span_pair.mp hc
  -- Key algebraic identity: c = (t₁ + u·y₂)·y₁ + (t₂ - u·y₁)·y₂ for any u ∈ T
  have halg : ∀ u : T,
      (↑c : T) = (t₁ + u * (↑y₂ : T)) * (↑y₁ : T) +
                  (t₂ - u * (↑y₁ : T)) * (↑y₂ : T) := by
    intro u
    have hceq : (↑c : T) = t₁ * (↑y₁ : T) + t₂ * (↑y₂ : T) := by
      rw [smul_eq_mul, smul_eq_mul] at hc_eq
      exact hc_eq.symm
    rw [hceq]
    ring
  -- It suffices to find x₁, x₂ transcendental over R with c = x₁·y₁ + x₂·y₂
  suffices ∃ (x₁ x₂ : T),
      (↑c : T) = x₁ * (↑y₁ : T) + x₂ * (↑y₂ : T) ∧
      x₁ ∈ adjoinLocSetY R x₁ y₂ ∧
      x₂ ∈ adjoinLocSetY R x₂ y₁ ∧
      Transcendental R.carrier x₁ ∧
      Transcendental R.carrier x₂ ∧
      (∃ S : NSubring T, IsAExtension R S ∧
        ∃ (hle : R.carrier ≤ S.carrier) (x₁' : S.carrier),
          (⟨(c : T), hle c.2⟩ : S.carrier) - x₁' * ⟨(y₁ : T), hle y₁.2⟩ ∈
            Ideal.span {⟨(y₂ : T), hle y₂.2⟩}) by
    obtain ⟨_, _, _, _, _, _, _, hS⟩ := this
    exact hS
  -- D₁, D₂ = values of u making x₁ = t₁+u·y₂ or x₂ = t₂-u·y₁ algebraic over R
  set D₁ : Set T := ⋃ (f : Polynomial R.carrier) (_ : f ≠ 0),
    {u : T | (aeval (t₁ + u * (↑y₂ : T)) f : T) = 0}
  set D₂ : Set T := ⋃ (f : Polynomial R.carrier) (_ : f ≠ 0),
    {u : T | (aeval (t₂ - u * (↑y₁ : T)) f : T) = 0}
  have hD₁_fiber_finite : ∀ (f : Polynomial R.carrier), f ≠ 0 →
      {u : T | (aeval (t₁ + u * (↑y₂ : T)) f : T) = 0}.Finite := by
    intro f hf
    have h_inj : Function.Injective fun (u : T) => t₁ + u * (↑y₂ : T) :=
      fun u₁ u₂ h => mul_right_cancel₀ hy₂ (add_left_cancel h)
    have hmap_ne : Polynomial.map R.carrier.subtype f ≠ 0 := by
      rw [Ne, ← Polynomial.map_zero R.carrier.subtype]
      exact (Polynomial.map_injective R.carrier.subtype Subtype.val_injective).ne hf
    rw [show {u : T | (aeval (t₁ + u * (↑y₂ : T)) f : T) = 0} =
        (fun u => t₁ + u * (↑y₂ : T)) ⁻¹'
          {x : T | (Polynomial.map R.carrier.subtype f).IsRoot x} from by
      ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq,
        Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def,
        show algebraMap R.carrier T = R.carrier.subtype from rfl]]
    exact (Polynomial.finite_setOf_isRoot hmap_ne).preimage
      (Set.InjOn.mono (Set.subset_univ _) h_inj.injOn)
  have hD₂_fiber_finite : ∀ (f : Polynomial R.carrier), f ≠ 0 →
      {u : T | (aeval (t₂ - u * (↑y₁ : T)) f : T) = 0}.Finite := by
    intro f hf
    have h_inj : Function.Injective fun (u : T) => t₂ - u * (↑y₁ : T) := by
      intro u₁ u₂ h
      dsimp only at h
      have h' : u₁ * (↑y₁ : T) = u₂ * (↑y₁ : T) := by
        rw [sub_eq_sub_iff_add_eq_add] at h
        exact add_left_cancel h.symm
      exact mul_right_cancel₀ hy₁ h'
    have hmap_ne : Polynomial.map R.carrier.subtype f ≠ 0 := by
      rw [Ne, ← Polynomial.map_zero R.carrier.subtype]
      exact (Polynomial.map_injective R.carrier.subtype Subtype.val_injective).ne hf
    rw [show {u : T | (aeval (t₂ - u * (↑y₁ : T)) f : T) = 0} =
        (fun u => t₂ - u * (↑y₁ : T)) ⁻¹'
          {x : T | (Polynomial.map R.carrier.subtype f).IsRoot x} from by
      ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq,
        Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def,
        show algebraMap R.carrier T = R.carrier.subtype from rfl]]
    exact (Polynomial.finite_setOf_isRoot hmap_ne).preimage
      (Set.InjOn.mono (Set.subset_univ _) h_inj.injOn)
  -- C_ext = {(0)} ∪ all associated primes of T/(r) for r ∈ R nonzero (the primes to avoid)
  set C_ext : Set (Ideal T) := {⊥} ∪
    ⋃ (r : R.carrier) (_ : (↑r : T) ≠ 0),
      (associatedPrimes T (T ⧸ Ideal.span {(↑r : T)}))
  have hC_ext_prime : ∀ P ∈ C_ext, P.IsPrime := by
    intro P hP
    rcases hP with rfl | hP
    · exact Ideal.isPrime_bot
    · rw [Set.mem_iUnion] at hP
      obtain ⟨r, hr⟩ := hP
      rw [Set.mem_iUnion] at hr
      obtain ⟨_, hP_ass⟩ := hr
      exact hP_ass.isPrime
  -- No prime in C_ext equals the maximal ideal (by hypothesis on T)
  have hC_ext_ne_M : ∀ P ∈ C_ext, P ≠ IsLocalRing.maximalIdeal T := by
    intro P hP hPM
    rcases hP with rfl | hP
    · exact hM_ne_bot hPM.symm
    · rw [Set.mem_iUnion] at hP
      obtain ⟨r, hr⟩ := hP
      rw [Set.mem_iUnion] at hr
      obtain ⟨hr_ne, hP_ass⟩ := hr
      exact hM_not_assoc (↑r) hr_ne (hPM ▸ hP_ass)
  -- D_mod₁ = lifts of roots of fbar mod P for each P ∈ C_ext (values u must avoid modulo P)
  set D_mod₁ : Set T := ⋃ (f : Polynomial R.carrier) (_ : f ≠ 0)
      (P : Ideal T) (_ : P ∈ C_ext) (_ : P ≠ ⊥)
      (_ : Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0)
      (_ : Ideal.Quotient.mk P (↑y₂ : T) ≠ 0),
    (Function.invFun (Ideal.Quotient.mk P)) ''
      {v : T ⧸ P | (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
        (Ideal.Quotient.mk P t₁ + v * Ideal.Quotient.mk P (↑y₂ : T)) = 0}
  set D_mod₂ : Set T := ⋃ (f : Polynomial R.carrier) (_ : f ≠ 0)
      (P : Ideal T) (_ : P ∈ C_ext) (_ : P ≠ ⊥)
      (_ : Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0)
      (_ : Ideal.Quotient.mk P (↑y₁ : T) ≠ 0),
    (Function.invFun (Ideal.Quotient.mk P)) ''
      {v : T ⧸ P | (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
        (Ideal.Quotient.mk P t₂ - v * Ideal.Quotient.mk P (↑y₁ : T)) = 0}
  set D_ext : Set T := D₁ ∪ D₂ ∪ D_mod₁ ∪ D_mod₂
  -- Finiteness of D_mod₁ fibers: fbar has finitely many roots in T/P (integral domain)
  have hD_mod₁_fiber_finite : ∀ (f : Polynomial R.carrier) (_ : f ≠ 0)
      (P : Ideal T) (_ : P ∈ C_ext) (_ : P ≠ ⊥)
      (hmap_ne : Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0)
      (hy₂_ne : Ideal.Quotient.mk P (↑y₂ : T) ≠ 0),
      ((Function.invFun (Ideal.Quotient.mk P)) ''
        {v : T ⧸ P | (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
          (Ideal.Quotient.mk P t₁ + v * Ideal.Quotient.mk P (↑y₂ : T)) = 0}).Finite := by
    intro f _ P hP hP_ne hmap_ne hy₂_ne
    haveI : P.IsPrime := hC_ext_prime P hP
    haveI : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
    have h_inj : Function.Injective
        fun (v : T ⧸ P) => Ideal.Quotient.mk P t₁ + v * Ideal.Quotient.mk P (↑y₂ : T) := by
      intro v₁ v₂ h
      have key : (v₁ - v₂) * Ideal.Quotient.mk P (↑y₂ : T) = 0 := by
        rw [sub_mul]
        exact sub_eq_zero.mpr (add_left_cancel h)
      exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hy₂_ne)
    apply Set.Finite.image
    exact (Polynomial.finite_setOf_isRoot hmap_ne).preimage
      (Set.InjOn.mono (Set.subset_univ _) h_inj.injOn)
  have hD_mod₂_fiber_finite : ∀ (f : Polynomial R.carrier) (_ : f ≠ 0)
      (P : Ideal T) (_ : P ∈ C_ext) (_ : P ≠ ⊥)
      (hmap_ne : Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0)
      (hy₁_ne : Ideal.Quotient.mk P (↑y₁ : T) ≠ 0),
      ((Function.invFun (Ideal.Quotient.mk P)) ''
        {v : T ⧸ P | (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
          (Ideal.Quotient.mk P t₂ - v * Ideal.Quotient.mk P (↑y₁ : T)) = 0}).Finite := by
    intro f _ P hP hP_ne hmap_ne hy₁_ne
    haveI : P.IsPrime := hC_ext_prime P hP
    haveI : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
    have h_inj : Function.Injective
        fun (v : T ⧸ P) => Ideal.Quotient.mk P t₂ - v * Ideal.Quotient.mk P (↑y₁ : T) := by
      intro v₁ v₂ h
      have key : (v₁ - v₂) * Ideal.Quotient.mk P (↑y₁ : T) = 0 := by
        rw [sub_mul]
        have := sub_right_injective h
        exact sub_eq_zero.mpr this
      exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hy₁_ne)
    apply Set.Finite.image
    exact (Polynomial.finite_setOf_isRoot hmap_ne).preimage
      (Set.InjOn.mono (Set.subset_univ _) h_inj.injOn)
  -- Cardinal bound for avoidance: |C_ext × D_ext| < |residue field| or both countable
  have hCD_bound : Cardinal.mk (↑C_ext × ↑D_ext) <
      Cardinal.mk (IsLocalRing.ResidueField T) ∨
      (C_ext.Countable ∧ D_ext.Countable) := by
    by_cases hR_le : Cardinal.mk R.carrier ≤ Cardinal.aleph0
    · -- R countable: use countable avoidance branch
      haveI : Countable R.carrier := Cardinal.mk_le_aleph0_iff.mp hR_le
      haveI : Countable (Polynomial R.carrier) :=
        Countable.of_equiv (ℕ →₀ R.carrier)
          { toFun := Polynomial.ofFinsupp
            invFun := Polynomial.toFinsupp
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      -- C_ext is countable: countable union of finite associated prime sets
      have hC_ext_countable : C_ext.Countable := by
        apply Set.Countable.union (Set.countable_singleton _)
        apply Set.countable_iUnion
        intro r
        apply Set.countable_iUnion
        intro _
        exact (associatedPrimes.finite T _).countable
      -- D₁ is a countable union of finite root sets
      have hD₁_countable : D₁.Countable := by
        apply Set.countable_iUnion
        intro f
        apply Set.countable_iUnion
        intro hf
        exact (hD₁_fiber_finite f hf).countable
      have hD₂_countable : D₂.Countable := by
        apply Set.countable_iUnion
        intro f
        apply Set.countable_iUnion
        intro hf
        exact (hD₂_fiber_finite f hf).countable
      -- D_mod₁ countable: countable polynomials × countable primes × finite root sets
      have hD_mod₁_countable : D_mod₁.Countable := by
        apply Set.countable_iUnion
        intro f
        apply Set.countable_iUnion
        intro hf_ne
        apply hC_ext_countable.biUnion
        intro P hP
        apply Set.countable_iUnion
        intro hP_ne
        apply Set.countable_iUnion
        intro hmap_ne
        apply Set.countable_iUnion
        intro hy₂_ne
        exact (hD_mod₁_fiber_finite f hf_ne P hP hP_ne hmap_ne hy₂_ne).countable
      have hD_mod₂_countable : D_mod₂.Countable := by
        apply Set.countable_iUnion
        intro f
        apply Set.countable_iUnion
        intro hf_ne
        apply hC_ext_countable.biUnion
        intro P hP
        apply Set.countable_iUnion
        intro hP_ne
        apply Set.countable_iUnion
        intro hmap_ne
        apply Set.countable_iUnion
        intro hy₁_ne
        exact (hD_mod₂_fiber_finite f hf_ne P hP hP_ne hmap_ne hy₁_ne).countable
      right
      exact ⟨hC_ext_countable,
        ((hD₁_countable.union hD₂_countable).union hD_mod₁_countable).union hD_mod₂_countable⟩
    · -- R uncountable: |C_ext × D_ext| ≤ |R|² = |R| < |T| = |residue field|
      left
      push Not at hR_le
      -- Key: |R| ≥ ℵ₀ allows infinite cardinal absorption (|R|·ℵ₀ = |R|² = |R|)
      have hR_inf : Cardinal.aleph0 ≤ Cardinal.mk R.carrier := le_of_lt hR_le
      -- |C_ext| ≤ |R|: it is {0} plus ≤ |R| associated primes, each finite
      have hC_le : Cardinal.mk C_ext ≤ Cardinal.mk R.carrier := by
        calc Cardinal.mk C_ext
            ≤ Cardinal.mk ↑({⊥} : Set (Ideal T)) +
              Cardinal.mk ↑(⋃ (r : R.carrier) (_ : (↑r : T) ≠ 0),
                associatedPrimes T (T ⧸ Ideal.span {(↑r : T)})) :=
              Cardinal.mk_union_le _ _
          _ ≤ 1 + Cardinal.mk R.carrier * Cardinal.aleph0 := by
              gcongr
              · exact Cardinal.mk_le_one_iff_set_subsingleton.mpr Set.subsingleton_singleton
              · apply (Cardinal.mk_iUnion_le _).trans
                gcongr
                apply ciSup_le'
                intro r
                apply Cardinal.mk_le_aleph0_iff.mpr
                by_cases hr : (r : T) = 0
                · exact Set.Countable.to_subtype (by simp [hr])
                · exact (Set.Finite.subset (associatedPrimes.finite T _)
                    (Set.iUnion_subset fun _ => le_refl _)).countable.to_subtype
          _ = Cardinal.mk R.carrier := by
              rw [Cardinal.mul_aleph0_eq hR_inf]
              exact Cardinal.add_eq_right hR_inf (one_le_aleph0.trans hR_inf)
      -- |D₁| ≤ |R|: union of |R[X]| = |R| polynomial fibers, each finite
      have hD₁_le : Cardinal.mk D₁ ≤ Cardinal.mk R.carrier := by
        calc Cardinal.mk D₁
            ≤ Cardinal.mk (Polynomial R.carrier) *
                ⨆ (f : Polynomial R.carrier), Cardinal.mk ↑(⋃ (_ : f ≠ 0),
                  {u : T | (aeval (t₁ + u * (↑y₂ : T)) f : T) = 0}) :=
              Cardinal.mk_iUnion_le _
          _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
              gcongr
              · exact Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf)
              · apply ciSup_le'
                intro f
                apply Cardinal.mk_le_aleph0_iff.mpr
                by_cases hf : f = 0
                · exact Set.Countable.to_subtype (by simp [hf])
                · exact (Set.Finite.subset (hD₁_fiber_finite f hf)
                    (Set.iUnion_subset fun _ => le_refl _)).countable.to_subtype
          _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
      have hD₂_le : Cardinal.mk D₂ ≤ Cardinal.mk R.carrier := by
        calc Cardinal.mk D₂
            ≤ Cardinal.mk (Polynomial R.carrier) *
                ⨆ (f : Polynomial R.carrier), Cardinal.mk ↑(⋃ (_ : f ≠ 0),
                  {u : T | (aeval (t₂ - u * (↑y₁ : T)) f : T) = 0}) :=
              Cardinal.mk_iUnion_le _
          _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
              gcongr
              · exact Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf)
              · apply ciSup_le'
                intro f
                apply Cardinal.mk_le_aleph0_iff.mpr
                by_cases hf : f = 0
                · exact Set.Countable.to_subtype (by simp [hf])
                · exact (Set.Finite.subset (hD₂_fiber_finite f hf)
                    (Set.iUnion_subset fun _ => le_refl _)).countable.to_subtype
          _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
      -- |D_mod₁| ≤ |R|: indexed by |R[X]| × |C_ext|, each fiber finite, so ≤ |R|² = |R|
      have hD_mod₁_le : Cardinal.mk D_mod₁ ≤ Cardinal.mk R.carrier := by
        calc Cardinal.mk D_mod₁
            ≤ Cardinal.mk (Polynomial R.carrier) *
                ⨆ (f : Polynomial R.carrier),
                  Cardinal.mk ↑(⋃ (_ : f ≠ 0)
                    (P : Ideal T) (_ : P ∈ C_ext) (_ : P ≠ ⊥)
                    (_ : Polynomial.map
                      ((Ideal.Quotient.mk P).comp R.carrier.subtype)
                      f ≠ 0)
                    (_ : Ideal.Quotient.mk P (↑y₂ : T) ≠ 0),
                    (Function.invFun (Ideal.Quotient.mk P)) ''
                      {v : T ⧸ P |
                        (Polynomial.map
                          ((Ideal.Quotient.mk P).comp
                            R.carrier.subtype) f).eval
                          (Ideal.Quotient.mk P t₁ +
                            v * Ideal.Quotient.mk P (↑y₂ : T)) =
                          0}) :=
              Cardinal.mk_iUnion_le _
          _ ≤ Cardinal.mk R.carrier * Cardinal.mk R.carrier := by
              gcongr
              · exact Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf)
              · apply ciSup_le'
                intro f
                by_cases hf : f = 0
                · simp [hf]
                · -- inner for f ≠ 0: union over C_ext of finite sets
                  have : (⋃ (_ : f ≠ 0)
                      (P : Ideal T) (_ : P ∈ C_ext)
                      (_ : P ≠ ⊥)
                      (_ : Polynomial.map
                        ((Ideal.Quotient.mk P).comp
                          R.carrier.subtype) f ≠ 0)
                      (_ : Ideal.Quotient.mk P (↑y₂ : T) ≠ 0),
                      (Function.invFun
                        (Ideal.Quotient.mk P)) ''
                        {v : T ⧸ P |
                          (Polynomial.map
                            ((Ideal.Quotient.mk P).comp
                              R.carrier.subtype) f).eval
                            (Ideal.Quotient.mk P t₁ +
                              v * Ideal.Quotient.mk P
                                (↑y₂ : T)) = 0}) ⊆
                    ⋃ P ∈ C_ext, ⋃ (_ : P ≠ ⊥)
                      (_ : Polynomial.map
                        ((Ideal.Quotient.mk P).comp
                          R.carrier.subtype) f ≠ 0)
                      (_ : Ideal.Quotient.mk P
                        (↑y₂ : T) ≠ 0),
                      (Function.invFun
                        (Ideal.Quotient.mk P)) ''
                        {v : T ⧸ P |
                          (Polynomial.map
                            ((Ideal.Quotient.mk P).comp
                              R.carrier.subtype) f).eval
                            (Ideal.Quotient.mk P t₁ +
                              v * Ideal.Quotient.mk P
                                (↑y₂ : T)) = 0} :=
                    Set.iUnion_subset fun _ => le_refl _
                  apply le_trans (Cardinal.mk_le_mk_of_subset this)
                  apply (Cardinal.mk_biUnion_le _ _).trans
                  apply le_trans (mul_le_mul' hC_le ?_)
                  · exact (Cardinal.mul_eq_self hR_inf).le
                  · apply ciSup_le'
                    intro ⟨P, hP⟩
                    apply le_trans (Cardinal.mk_le_aleph0_iff.mpr _) hR_inf
                    apply Set.Countable.to_subtype
                    by_cases hP_ne : P = ⊥
                    · simp [hP_ne]
                    · apply Set.countable_iUnion
                      intro _
                      apply Set.countable_iUnion
                      intro hmap_ne
                      apply Set.countable_iUnion
                      intro hy₂_ne
                      exact (hD_mod₁_fiber_finite f hf P hP hP_ne hmap_ne hy₂_ne).countable
          _ = Cardinal.mk R.carrier := Cardinal.mul_eq_self hR_inf
      -- |D_mod₂| ≤ |R| by the same argument as D_mod₁
      have hD_mod₂_le : Cardinal.mk D_mod₂ ≤ Cardinal.mk R.carrier := by
        calc Cardinal.mk D_mod₂
            ≤ Cardinal.mk (Polynomial R.carrier) *
                ⨆ (f : Polynomial R.carrier),
                  Cardinal.mk ↑(⋃ (_ : f ≠ 0)
                    (P : Ideal T) (_ : P ∈ C_ext)
                    (_ : P ≠ ⊥)
                    (_ : Polynomial.map
                      ((Ideal.Quotient.mk P).comp
                        R.carrier.subtype) f ≠ 0)
                    (_ : Ideal.Quotient.mk P
                      (↑y₁ : T) ≠ 0),
                    (Function.invFun
                      (Ideal.Quotient.mk P)) ''
                      {v : T ⧸ P |
                        (Polynomial.map
                          ((Ideal.Quotient.mk P).comp
                            R.carrier.subtype) f).eval
                          (Ideal.Quotient.mk P t₂ -
                            v * Ideal.Quotient.mk P
                              (↑y₁ : T)) = 0}) :=
              Cardinal.mk_iUnion_le _
          _ ≤ Cardinal.mk R.carrier *
              Cardinal.mk R.carrier := by
              gcongr
              · exact Polynomial.cardinalMk_le_max.trans
                  (max_le le_rfl hR_inf)
              · apply ciSup_le'
                intro f
                by_cases hf : f = 0
                · simp [hf]
                · have : (⋃ (_ : f ≠ 0)
                      (P : Ideal T) (_ : P ∈ C_ext)
                      (_ : P ≠ ⊥)
                      (_ : Polynomial.map
                        ((Ideal.Quotient.mk P).comp
                          R.carrier.subtype) f ≠ 0)
                      (_ : Ideal.Quotient.mk P
                        (↑y₁ : T) ≠ 0),
                      (Function.invFun
                        (Ideal.Quotient.mk P)) ''
                        {v : T ⧸ P |
                          (Polynomial.map
                            ((Ideal.Quotient.mk P).comp
                              R.carrier.subtype) f).eval
                            (Ideal.Quotient.mk P t₂ -
                              v * Ideal.Quotient.mk P
                                (↑y₁ : T)) = 0}) ⊆
                    ⋃ P ∈ C_ext, ⋃ (_ : P ≠ ⊥)
                      (_ : Polynomial.map
                        ((Ideal.Quotient.mk P).comp
                          R.carrier.subtype) f ≠ 0)
                      (_ : Ideal.Quotient.mk P
                        (↑y₁ : T) ≠ 0),
                      (Function.invFun
                        (Ideal.Quotient.mk P)) ''
                        {v : T ⧸ P |
                          (Polynomial.map
                            ((Ideal.Quotient.mk P).comp
                              R.carrier.subtype) f).eval
                            (Ideal.Quotient.mk P t₂ -
                              v * Ideal.Quotient.mk P
                                (↑y₁ : T)) = 0} :=
                    Set.iUnion_subset fun _ => le_refl _
                  apply le_trans (Cardinal.mk_le_mk_of_subset this)
                  apply (Cardinal.mk_biUnion_le _ _).trans
                  apply le_trans (mul_le_mul' hC_le ?_)
                  · exact (Cardinal.mul_eq_self hR_inf).le
                  · apply ciSup_le'
                    intro ⟨P, hP⟩
                    apply le_trans (Cardinal.mk_le_aleph0_iff.mpr _) hR_inf
                    apply Set.Countable.to_subtype
                    by_cases hP_ne : P = ⊥
                    · simp [hP_ne]
                    · apply Set.countable_iUnion
                      intro _
                      apply Set.countable_iUnion
                      intro hmap_ne
                      apply Set.countable_iUnion
                      intro hy₁_ne
                      exact (hD_mod₂_fiber_finite f hf P hP hP_ne hmap_ne hy₁_ne).countable
          _ = Cardinal.mk R.carrier := Cardinal.mul_eq_self hR_inf
      have hD_le : Cardinal.mk D_ext ≤ Cardinal.mk R.carrier := by
        apply le_trans (Cardinal.mk_union_le _ _)
        apply le_trans (add_le_add (Cardinal.mk_union_le _ _) hD_mod₂_le)
        apply le_trans (add_le_add (add_le_add (Cardinal.mk_union_le _ _) hD_mod₁_le) le_rfl)
        apply le_trans (add_le_add (add_le_add (add_le_add hD₁_le hD₂_le) le_rfl) le_rfl)
        rw [Cardinal.add_eq_left hR_inf le_rfl,
            Cardinal.add_eq_left hR_inf le_rfl,
            Cardinal.add_eq_left hR_inf le_rfl]
      -- Final chain: |C_ext × D_ext| ≤ |R|² = |R| < |T| = |k|
      calc Cardinal.mk (↑C_ext × ↑D_ext)
          = Cardinal.mk C_ext * Cardinal.mk D_ext := (Cardinal.mul_def _ _).symm
        _ ≤ Cardinal.mk R.carrier * Cardinal.mk R.carrier := mul_le_mul' hC_le hD_le
        _ = Cardinal.mk R.carrier := Cardinal.mul_eq_self hR_inf
        _ < Cardinal.mk T := hR_card
        _ = Cardinal.mk (IsLocalRing.ResidueField T) := hT_card
  -- Apply prime avoidance to obtain u ∉ ⋃ (P + {r}) for all P ∈ C_ext, r ∈ D_ext
  obtain ⟨u, _, hu_avoid⟩ := avoidance hC_ext_prime hC_ext_ne_M
    (D := D_ext) hCD_bound (I := ⊤)
    (fun P hP hle => (hC_ext_prime P hP).ne_top (top_le_iff.mp hle))
  -- x₁ = t₁ + u·y₂ is transcendental: algebraic relation would put u ∈ D₁, contradicting avoidance
  have hx₁_trans : Transcendental R.carrier (t₁ + u * (↑y₂ : T)) := by
    rw [Transcendental]
    intro ⟨f, hf_ne, hf_eval⟩
    exact hu_avoid ⊥ (Set.mem_union_left _ rfl) u
      (Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left D₂
          (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf_ne, hf_eval⟩⟩))))
      ⟨0, (⊥ : Ideal T).zero_mem, u, rfl, by simp⟩
  -- x₂ = t₂ - u·y₁ is transcendental by the same argument via D₂
  have hx₂_trans : Transcendental R.carrier (t₂ - u * (↑y₁ : T)) := by
    rw [Transcendental]
    intro ⟨f, hf_ne, hf_eval⟩
    exact hu_avoid ⊥ (Set.mem_union_left _ rfl) u
      (Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right D₁
          (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf_ne, hf_eval⟩⟩))))
      ⟨0, (⊥ : Ideal T).zero_mem, u, rfl, by simp⟩
  have hC_ext_mem : ∀ (p : R.carrier), (↑p : T) ≠ 0 →
      ∀ P, P ∈ associatedPrimes T (T ⧸ Ideal.span {(↑p : T)}) → P ∈ C_ext :=
    fun p hp_ne P hP_ass => Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp_ne, hP_ass⟩⟩)
  have hD_ext_invFun₁ : ∀ (f : Polynomial R.carrier), f ≠ 0 →
      ∀ (P : Ideal T), P ∈ C_ext → P ≠ ⊥ →
      Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0 →
      Ideal.Quotient.mk P (↑y₂ : T) ≠ 0 →
      ∀ v₀, v₀ ∈ {v : T ⧸ P |
        (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
          (Ideal.Quotient.mk P t₁ + v * Ideal.Quotient.mk P (↑y₂ : T)) = 0} →
      Function.invFun (Ideal.Quotient.mk P) v₀ ∈ D_ext :=
    fun f hf_ne P hPC hPne hmap_ne hy₂_ne v₀ hv₀ =>
      Set.mem_union_left _ (Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf_ne,
          Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hPC,
            Set.mem_iUnion.mpr ⟨hPne, Set.mem_iUnion.mpr ⟨hmap_ne,
              Set.mem_iUnion.mpr ⟨hy₂_ne, ⟨v₀, hv₀, rfl⟩⟩⟩⟩⟩⟩⟩⟩))
  have hD_ext_invFun₂ : ∀ (f : Polynomial R.carrier), f ≠ 0 →
      ∀ (P : Ideal T), P ∈ C_ext → P ≠ ⊥ →
      Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f ≠ 0 →
      Ideal.Quotient.mk P (↑y₁ : T) ≠ 0 →
      ∀ v₀, v₀ ∈ {v : T ⧸ P |
        (Polynomial.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) f).eval
          (Ideal.Quotient.mk P t₂ - v * Ideal.Quotient.mk P (↑y₁ : T)) = 0} →
      Function.invFun (Ideal.Quotient.mk P) v₀ ∈ D_ext :=
    fun f hf_ne P hPC hPne hmap_ne hy₁_ne v₀ hv₀ =>
      Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf_ne,
          Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hPC,
            Set.mem_iUnion.mpr ⟨hPne, Set.mem_iUnion.mpr ⟨hmap_ne,
              Set.mem_iUnion.mpr ⟨hy₁_ne, ⟨v₀, hv₀, rfl⟩⟩⟩⟩⟩⟩⟩⟩)
  -- Kernel proofs: for each height-≤-1 prime P, if p ∈ P is prime in R then C(p) | f
  have hx₁_ker_pf := intersection_close_up_ker_pf₁ R y₂ t₁ u
    C_ext D_ext hC_ext_mem hD_ext_invFun₁ hu_avoid
  have hx₂_ker_pf := intersection_close_up_ker_pf₂ R y₁ t₂ u
    C_ext D_ext hC_ext_mem hD_ext_invFun₂ hu_avoid
  refine ⟨t₁ + u * ↑y₂, t₂ - u * ↑y₁, halg u,
    x_mem_adjoinLocSetY R _ y₂, x_mem_adjoinLocSetY R _ y₁,
    hx₁_trans, hx₂_trans, ?_⟩
  -- Build Rbar = R[x₁,y₂⁻¹] ∩ R[x₂,y₁⁻¹] and localize at M to get the A-extension S
  obtain ⟨S, hAext, hx₁_mem, hx₂_mem⟩ := build_intersection_nsubring R
    (t₁ + u * ↑y₂) (t₂ - u * ↑y₁) y₁ y₂ c (halg u)
    hx₁_trans hx₂_trans hcoprime hy₁ hy₂
    hM_ne_bot hM_not_assoc hAss_ht hR_card hT_card
    hx₁_ker_pf hx₂_ker_pf
  -- c - x₁·y₁ = x₂·y₂ ∈ (y₂)S, completing the close-up
  exact ⟨S, hAext, hAext.le, ⟨_, hx₁_mem⟩, Ideal.mem_span_singleton.mpr
    ⟨⟨_, hx₂_mem⟩, Subtype.ext (show (↑c : T) - (t₁ + u * ↑y₂) * ↑y₁ =
      ↑y₂ * (t₂ - u * ↑y₁) from by linear_combination halg u)⟩⟩
⟩

/- Coprime close-up via Krull domain intersection (Heitmann Lemma 4).

Given R an NSubring, y₁ y₂ ∈ R coprime non-units with (y₁:T) ≠ 0 and (y₂:T) ≠ 0,
and c ∈ (y₁,y₂)·T ∩ R, construct an A-extension S with c ∈ (y₁,y₂)·S.

The construction: choose x₁ = t₁ + u·y₂ transcendental, set x₂ = t₂ - u·y₁,
build Rbar = R[x₁,y₂⁻¹] ∩ R[x₂,y₁⁻¹], localize at M to get S.
Then c = x₁·y₁ + x₂·y₂ ∈ (y₁,y₂)·S since x₁ ∈ A₁ ⊆ S, x₂ ∈ A₂ ⊆ S. -/
include T in theorem
  intersection_close_up
    (R : NSubring T) (y₁ y₂ : R.carrier) (c : R.carrier)
    (hc : (c : T) ∈ Ideal.span {(y₁ : T), (y₂ : T)})
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥)
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
  exact
    (intersection_close_up_proof
      R y₁ y₂ c hc hcoprime hy₁ hy₂ hM_ne_bot hM_not_assoc hAss_ht hR_card hT_card
    ).down

end MainTheorem

end
