/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.KrullDomain.UFDConstruction
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Krull domain intersection construction

Constructs the intersection NSubring for the Anderson--Jensen
proof. Starting from two adjoin-localisation subrings, one shows
the intersection is a Noetherian UFD whose primes have height
at most one in T, using well-founded descent on heights and the
mod-principal transcendence argument.
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/- Derive mod-principal transcendence from the stronger mod-P version.
If for every associated prime P of T/(p) with y ∉ P, the polynomial
evaluation aeval x f ∈ P implies C(p) | f, then aeval x f ∈ span{p}
already implies C(p) | f. -/
include T in theorem derive_mod_principal_trans
    (R : NSubring T) (x : T) (y : R.carrier)
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hx_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x f ∈ P → (C p : Polynomial R.carrier) ∣ f)
    (p : R.carrier) (hp : Prime p) (hpy : ¬p ∣ y)
    (f : Polynomial R.carrier)
    (hf_mem : aeval x f ∈ Ideal.span {(↑p : T)}) :
    (C p : Polynomial R.carrier) ∣ f := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  -- Lift nonzero-ness of the prime p from R to T via the subring injection
  have hp_ne : (↑p : T) ≠ 0 := fun h => hp.ne_zero (R.carrier.subtype_injective h)
  have hnt : Nontrivial (T ⧸ Ideal.span {(↑p : T)}) := by
    rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    intro ⟨c', hc'⟩
    have hmem : p ∈ IsLocalRing.maximalIdeal R.carrier :=
      (IsLocalRing.mem_maximalIdeal _).mpr hp.not_unit
    rw [R.maximal_ideal_eq, Ideal.mem_comap] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_of_dvd_one ⟨c', hc'⟩)
  -- Pick an associated prime P of T/(p); it contains span{p} and has height ≤ 1
  obtain ⟨P, hP_mem⟩ := associatedPrimes.nonempty (R := T) (M := T ⧸ Ideal.span {(↑p : T)})
  have hP_prime : P.IsPrime := hP_mem.isPrime
  have hI_le_P : Ideal.span {(↑p : T)} ≤ P := by
    have h := hP_mem.annihilator_le
    rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at h
  have hp_P : (↑p : T) ∈ P := hI_le_P (Ideal.mem_span_singleton_self _)
  have hP_ne_top : P ≠ ⊤ := hP_prime.ne_top
  have hP_ht : P.height ≤ 1 := hAss_ht _ hp_ne P hP_mem
  have hR_ht := R.height_bound _ hp_ne P hP_mem
  haveI : (P.comap R.carrier.subtype).IsPrime := Ideal.comap_isPrime _ _
  have hspan_le : Ideal.span {p} ≤ P.comap R.carrier.subtype :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (show (↑p : T) ∈ P from hp_P))
  have hspan_ne : Ideal.span {p} ≠ (⊥ : Ideal R.carrier) :=
    Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  haveI : (Ideal.span {p}).IsPrime :=
    (Ideal.span_singleton_prime (α := R.carrier) hp.ne_zero).mpr hp
  -- Since R is a UFD and P∩R has height ≤ 1, the prime ideal (p) must equal P∩R
  have hspan_eq : Ideal.span {p} = P.comap R.carrier.subtype := by
    by_contra hne
    have hstrict := lt_of_le_of_ne hspan_le hne
    rw [show (1 : ℕ∞) = ↑(1 : ℕ) from rfl] at hR_ht
    rw [Ideal.height_le_iff] at hR_ht
    have hspan_ht := hR_ht (Ideal.span {p}) inferInstance hstrict
    have hbot_lt := bot_lt_iff_ne_bot.mpr hspan_ne
    have hbot_fin : (⊥ : Ideal R.carrier).FiniteHeight :=
      ⟨Or.inr (by simp [Ideal.height_bot])⟩
    have h0 := @Ideal.height_strict_mono_of_isPrime R.carrier _
      (⊥ : Ideal R.carrier) (Ideal.span {p}) Ideal.isPrime_bot hbot_lt hbot_fin
    rw [Ideal.height_bot] at h0
    rw [show (↑(1 : ℕ) : ℕ∞) = 1 from rfl, Order.lt_one_iff] at hspan_ht
    rw [hspan_ht] at h0
    exact lt_irrefl _ h0
  -- y ∉ P because p ∤ y and (p) = P∩R
  have hy_nP : (↑y : T) ∉ P := by
    intro hyP
    have : y ∈ P.comap R.carrier.subtype := hyP
    rw [← hspan_eq] at this
    exact hpy (Ideal.mem_span_singleton.mp this)
  -- Apply the mod-P kernel hypothesis to conclude C(p) | f
  exact hx_ker P hP_prime hP_ne_top hP_ht hy_nP p hp hp_P f (hI_le_P hf_mem)

/-!
## Section 4: Main Close-Up Theorem

The Krull domain intersection construction produces an NSubring S that is
an A-extension of R with c ∈ (y₁,y₂)·S.
-/

section MainTheorem

variable [IsAdicComplete (IsLocalRing.maximalIdeal T) T]

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/- Well-founded descent argument for the height bound: if P ∩ R ≠ ⊥ and
every element of P ∩ S_sub is divisible by a prime p₀ generating P ∩ R,
then every nonzero element of any prime q ⊊ P ∩ S_sub would be infinitely
divisible by p₀, contradicting WfDvdMonoid. Hence q = ⊥, giving the
height bound contradiction. -/
include T in theorem height_bound_wf_descent
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier)
    (S_sub : Subring T) [IsDomain S_sub] [WfDvdMonoid S_sub]
    (hR_le : R.carrier ≤ S_sub)
    (hRbar_le_S : ∀ t, t ∈ intersectionSet R x₁ x₂ y₁ y₂ →
      t ∈ (S_sub : Set T))
    (hinv : ∀ (s : S_sub),
      (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (hR_prime_in_S : ∀ (p : R.carrier), Prime p →
      (↑p : T) ∈ IsLocalRing.maximalIdeal T →
      Prime (⟨(↑p : T), hR_le p.2⟩ : S_sub))
    (hS_mem_rep : ∀ s : S_sub,
      ∃ (a b : T), a ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ (s : T) * b = a)
    (P : Ideal T) [hP_prime : P.IsPrime]
    (hP_ht : P.height ≤ 1)
    (hR_bound : (P.comap R.carrier.subtype).height ≤ 1)
    (hPR_bot : P.comap R.carrier.subtype ≠ ⊥)
    (hP_le_M : P ≤ IsLocalRing.maximalIdeal T)
    (x_eval : T) (y_elem : R.carrier)
    (hy_nP : (↑y_elem : T) ∉ P)
    (hx_ker : ∀ (P' : Ideal T), P'.IsPrime → P' ≠ ⊤ → P'.height ≤ 1 →
      (↑y_elem : T) ∉ P' →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P' →
      ∀ (f : Polynomial R.carrier),
        aeval x_eval f ∈ P' → (C p : Polynomial R.carrier) ∣ f)
    (heval_S : ∀ f : Polynomial R.carrier, (aeval x_eval f : T) ∈ S_sub)
    (get_witness : ∀ t, t ∈ intersectionSet R x₁ x₂ y₁ y₂ →
      ∃ (f : Polynomial R.carrier) (n : ℕ),
        t * (↑y_elem : T) ^ n = aeval x_eval f)
    (q : Ideal S_sub) [hq_prime : q.IsPrime]
    (hq_lt : q < Ideal.comap S_sub.subtype P)
    (s : S_sub) (hs_ne : s ≠ 0) (hs_q : s ∈ q) :
    False := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  haveI : (Ideal.comap R.carrier.subtype P).IsPrime := Ideal.comap_isPrime _ _
  -- Since P∩R ≠ ⊥ and R is a UFD, pick a prime generator p₀ of P∩R
  obtain ⟨p₀, hp₀_prime, hp₀_mem⟩ :=
    exists_prime_mem_of_ne_bot (Ideal.comap R.carrier.subtype P) hPR_bot
  have hspan_ne_bot : Ideal.span {p₀} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact hp₀_prime.ne_zero
  haveI : (Ideal.span {p₀}).IsPrime :=
    Ideal.span_singleton_prime hp₀_prime.ne_zero |>.mpr hp₀_prime
  have hspan_le : Ideal.span {p₀} ≤ Ideal.comap R.carrier.subtype P :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp₀_mem)
  -- Height-1 argument: (p₀) = P∩R since there is no room for a strict inclusion
  have hspan_eq : Ideal.span {p₀} = Ideal.comap R.carrier.subtype P := by
    by_contra hne
    have hstrict : Ideal.span {p₀} < Ideal.comap R.carrier.subtype P :=
      lt_of_le_of_ne hspan_le hne
    have hht' : (Ideal.comap R.carrier.subtype P).height ≤ ↑(1 : ℕ) := hR_bound
    rw [Ideal.height_le_iff] at hht'
    have hspan_height : (Ideal.span {p₀}).height < ↑(1 : ℕ) :=
      hht' _ inferInstance hstrict
    have hbot_lt : (⊥ : Ideal R.carrier) < Ideal.span {p₀} :=
      bot_lt_iff_ne_bot.mpr hspan_ne_bot
    have hbot_fin : (⊥ : Ideal R.carrier).FiniteHeight :=
      ⟨Or.inr (by simp [Ideal.height_bot])⟩
    have h0 : (⊥ : Ideal R.carrier).height < (Ideal.span {p₀}).height :=
      @Ideal.height_strict_mono_of_isPrime R.carrier _ (⊥ : Ideal R.carrier)
        (Ideal.span {p₀}) Ideal.isPrime_bot hbot_lt hbot_fin
    rw [Ideal.height_bot] at h0
    rw [show (↑(1 : ℕ) : ℕ∞) = 1 from rfl, Order.lt_one_iff] at hspan_height
    rw [hspan_height] at h0
    exact lt_irrefl _ h0
  have hp₀_P : (↑p₀ : T) ∈ P :=
    (hspan_eq ▸ Ideal.mem_span_singleton_self p₀ : p₀ ∈ Ideal.comap R.carrier.subtype P)
  have hp₀_not_unit_T : ¬IsUnit (↑p₀ : T) :=
    fun hu => hP_prime.ne_top (P.eq_top_of_isUnit_mem hp₀_P hu)
  set p₀_S : S_sub := ⟨(↑p₀ : T), hR_le p₀.2⟩
  have hp₀_M : (↑p₀ : T) ∈ IsLocalRing.maximalIdeal T := hP_le_M hp₀_P
  have hp₀_prime_S : Prime p₀_S := hR_prime_in_S p₀ hp₀_prime hp₀_M
  have hP_ne_top : P ≠ ⊤ := hP_prime.ne_top
  -- Key divisibility: every element of P∩S is divisible by p₀ in S
  have hdiv_p₀ : ∀ (a : S_sub), (a : T) ∈ P →
      ∃ (b : S_sub), (a : T) = (↑p₀ : T) * (b : T) := by
    intro a ha_P
    obtain ⟨u_val, v_val, hu_Rbar, hv_Rbar, hv_nM, hav⟩ := hS_mem_rep a
    have hu_P : u_val ∈ P := hav ▸ P.mul_mem_right v_val ha_P
    obtain ⟨g, m, hgm⟩ := get_witness u_val hu_Rbar
    have heval_P : (aeval x_eval g : T) ∈ P := hgm ▸ P.mul_mem_right _ hu_P
    -- Mod-P transcendence: since aeval(g) ∈ P and y ∉ P, we get C(p₀) | g
    have hCp₀_dvd := hx_ker P hP_prime hP_ne_top hP_ht hy_nP
      p₀ hp₀_prime hp₀_P g heval_P
    obtain ⟨g', hgg'⟩ := hCp₀_dvd
    have hprod_eq : u_val * (↑y_elem : T) ^ m = (↑p₀ : T) * (aeval x_eval g' : T) := by
      rw [hgm, hgg', map_mul, Polynomial.aeval_C]
      rfl
    have hu_S : u_val ∈ S_sub := hRbar_le_S _ hu_Rbar
    have hym_S : (↑y_elem : T) ^ m ∈ S_sub := S_sub.pow_mem (hR_le y_elem.2) m
    have hg'_S : (aeval x_eval g' : T) ∈ S_sub := heval_S g'
    have hdvd_prod : p₀_S ∣ (⟨u_val, hu_S⟩ : S_sub) * ⟨(↑y_elem : T) ^ m, hym_S⟩ :=
      ⟨⟨aeval x_eval g', hg'_S⟩, Subtype.ext hprod_eq⟩
    have hp₀_ndvd_y : ¬(p₀_S ∣ (⟨(↑y_elem : T), hR_le y_elem.2⟩ : S_sub)) := by
      intro ⟨c, hc⟩
      have : (↑y_elem : T) ∈ P := by
        have hval : (↑y_elem : T) = (↑p₀ : T) * (c : T) := congrArg Subtype.val hc
        rw [hval]
        exact P.mul_mem_right _ hp₀_P
      exact hy_nP this
    have hp₀_ndvd_ym : ¬(p₀_S ∣ (⟨(↑y_elem : T) ^ m, hym_S⟩ : S_sub)) := by
      intro hdvd
      apply hp₀_ndvd_y
      have : p₀_S ∣ ⟨(↑y_elem : T), hR_le y_elem.2⟩ ^ m := by
        convert hdvd using 1
      exact hp₀_prime_S.dvd_of_dvd_pow this
    -- p₀ | u·yⁿ and p₀ ∤ yⁿ (since y ∉ P), so by primality p₀ | u
    have hdvd_u : p₀_S ∣ (⟨u_val, hu_S⟩ : S_sub) :=
      (hp₀_prime_S.dvd_or_dvd hdvd_prod).resolve_right hp₀_ndvd_ym
    obtain ⟨u', hu'_eq⟩ := hdvd_u
    have hv_S : v_val ∈ S_sub := hRbar_le_S _ hv_Rbar
    have hv_unit_S : IsUnit (⟨v_val, hv_S⟩ : S_sub) := hinv ⟨v_val, hv_S⟩ hv_nM
    obtain ⟨v_unit, hv_unit_eq⟩ := hv_unit_S
    refine ⟨u' * ↑v_unit⁻¹, ?_⟩
    have hv_val_eq : (↑v_unit : S_sub).val = v_val := congrArg Subtype.val hv_unit_eq
    have hav_S : a * ↑v_unit = ⟨u_val, hu_S⟩ := Subtype.ext (by
      simp only [Subring.coe_mul]
      rw [hv_val_eq]
      exact hav)
    have hav_S2 : a * ↑v_unit = p₀_S * u' := hav_S.trans hu'_eq
    have heq_S : a = p₀_S * u' * ↑v_unit⁻¹ := by
      rw [Units.eq_mul_inv_iff_mul_eq]
      exact hav_S2
    have heq_T := congrArg Subtype.val heq_S
    simp only [Subring.coe_mul] at heq_T ⊢
    rw [heq_T, show (p₀_S : T) = (↑p₀ : T) from rfl, mul_assoc]
  -- p₀ ∉ q, else q would contain all of P∩S, contradicting q ⊊ P∩S
  have hp₀_nq : p₀_S ∉ q := by
    intro hp₀q
    have hsub : Ideal.comap S_sub.subtype P ≤ q := by
      intro a ha_PS
      obtain ⟨b, hb_eq⟩ := hdiv_p₀ a ha_PS
      have hab : a = p₀_S * b := Subtype.ext hb_eq
      rw [hab]
      exact Ideal.mul_mem_right b q hp₀q
    exact lt_irrefl q (lt_of_lt_of_le hq_lt hsub)
  -- Well-founded descent on T-divisibility: every s ∈ q is divisible by p₀, so s/p₀ ∈ q, repeat
  apply hs_ne
  suffices h : ∀ (w : T), ∀ (a : S_sub), (a : T) = w → a ∈ q → a = 0 from
    h (s : T) s rfl hs_q
  intro w
  apply (wellFounded_dvdNotUnit (α := T)).induction w
  intro w ih a haw ha_q
  by_contra ha_ne
  have ha_ne_T : (a : T) ≠ 0 := fun h => ha_ne (Subtype.ext h)
  have ha_P : (a : T) ∈ P := hq_lt.le ha_q
  obtain ⟨b, hb_eq⟩ := hdiv_p₀ a ha_P
  have hb_ne_T : (b : T) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hb_eq
    exact ha_ne_T (haw ▸ hb_eq)
  have hab : a = p₀_S * b := Subtype.ext hb_eq
  have hb_q : b ∈ q :=
    (hq_prime.mem_or_mem (hab ▸ ha_q)).resolve_left hp₀_nq
  have hdvd : DvdNotUnit (b : T) w :=
    ⟨hb_ne_T, (↑p₀ : T), hp₀_not_unit_T, haw.symm.trans (hb_eq.trans (mul_comm _ _))⟩
  exact ha_ne (Subtype.ext (by
    have hb0 := ih (b : T) hdvd b rfl hb_q
    simp [hb_eq, congrArg Subtype.val hb0]))

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/-- Height bound for primes of S_sub: every associated prime P of T/(t)
contracts to an ideal of height ≤ 1 in S_sub. Uses the K[X] PID argument
for the P∩R = ⊥ case and well-founded descent for P∩R ≠ ⊥. -/
private def build_height_bound_proof
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier)
    (S_sub : Subring T) [UniqueFactorizationMonoid S_sub]
    (hR_le : R.carrier ≤ S_sub)
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hx₁_trans : Transcendental R.carrier x₁)
    (hx₂_trans : Transcendental R.carrier x₂)
    (hx₁_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₂ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₁ f ∈ P → (C p : Polynomial R.carrier) ∣ f)
    (hx₂_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₁ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₂ f ∈ P → (C p : Polynomial R.carrier) ∣ f)
    (hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (hR_prime_in_S : ∀ (p : R.carrier), Prime p →
      (↑p : T) ∈ IsLocalRing.maximalIdeal T →
      Prime (⟨(↑p : T), hR_le p.2⟩ : S_sub))
    (hS_sub_eq : (S_sub : Set T) =
      {t : T | ∃ (a : T) (b : T),
        a ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a})
    (hRbar_le_S : ∀ t, t ∈ intersectionSet R x₁ x₂ y₁ y₂ → t ∈ (S_sub : Set T))
    (hx₁_Rbar : x₁ ∈ intersectionSet R x₁ x₂ y₁ y₂)
    (hx₂_Rbar : x₂ ∈ intersectionSet R x₁ x₂ y₁ y₂) : PLift (
    ∀ (t : T), t ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
        Ideal.height (P.comap S_sub.subtype) ≤ 1 ) := ⟨by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  -- Set up Rbar = R[x₁,y₂⁻¹] ∩ R[x₂,y₁⁻¹] and its localization S = Rbar[units⁻¹]
  set Rbar := intersectionSet R x₁ x₂ y₁ y₂
  set S_carrier : Set T :=
    {t : T | ∃ (a : T) (b : T), a ∈ Rbar ∧ b ∈ Rbar ∧
      b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a}
  have hS_sub_eq' : (S_sub : Set T) = S_carrier := hS_sub_eq
  have hRbar_one : (1 : T) ∈ Rbar :=
    ⟨⟨C 1, 0, by simp⟩, ⟨C 1, 0, by simp⟩⟩
  have hRbar_add : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ + t₂ ∈ Rbar := by
    intro t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩
    constructor
    · obtain ⟨f₁, n₁, hf₁⟩ := h₁₁
      obtain ⟨f₂, n₂, hf₂⟩ := h₂₁
      refine ⟨f₁ * C (y₂ ^ n₂) + f₂ * C (y₂ ^ n₁), n₁ + n₂, ?_⟩
      have key : (t₁ + t₂) * (↑y₂ : T) ^ (n₁ + n₂) =
          t₁ * (↑y₂ : T) ^ n₁ * (↑y₂ : T) ^ n₂ +
          t₂ * (↑y₂ : T) ^ n₂ * (↑y₂ : T) ^ n₁ := by rw [pow_add]
                                                     ring
      rw [key, hf₁, hf₂, map_add, map_mul, map_mul, aeval_C, aeval_C]
      simp only [show algebraMap R.carrier T = R.carrier.subtype from rfl,
        Subring.coe_subtype, map_pow]
    · obtain ⟨f₁, n₁, hf₁⟩ := h₁₂
      obtain ⟨f₂, n₂, hf₂⟩ := h₂₂
      refine ⟨f₁ * C (y₁ ^ n₂) + f₂ * C (y₁ ^ n₁), n₁ + n₂, ?_⟩
      have key : (t₁ + t₂) * (↑y₁ : T) ^ (n₁ + n₂) =
          t₁ * (↑y₁ : T) ^ n₁ * (↑y₁ : T) ^ n₂ +
          t₂ * (↑y₁ : T) ^ n₂ * (↑y₁ : T) ^ n₁ := by rw [pow_add]
                                                     ring
      rw [key, hf₁, hf₂, map_add, map_mul, map_mul, aeval_C, aeval_C]
      simp only [show algebraMap R.carrier T = R.carrier.subtype from rfl,
        Subring.coe_subtype, map_pow]
  have hRbar_mul : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ * t₂ ∈ Rbar :=
    fun t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩ =>
      ⟨(fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₁ y₂ t₁ t₂ h₁₁ h₂₁,
       (fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₂ y₁ t₁ t₂ h₁₂ h₂₂⟩
  have hS_mem_rep : ∀ s : S_sub,
      ∃ (a b : T), a ∈ Rbar ∧ b ∈ Rbar ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ (s : T) * b = a := by
    intro s
    have := s.2
    change s.1 ∈ (S_sub : Set T) at this
    rw [hS_sub_eq'] at this
    exact this
  -- Main argument: show (P∩S) has height ≤ 1 for each associated prime P of T/(t)
  intro t ht_ne P hP
  have hP_prime : P.IsPrime := hP.isPrime
  haveI : (Ideal.comap S_sub.subtype P).IsPrime := hP_prime.comap _
  have hP_ht : P.height ≤ 1 := hAss_ht t ht_ne P hP
  have hP_ne_M : P ≠ IsLocalRing.maximalIdeal T := fun h =>
    hM_not_assoc t ht_ne (h ▸ hP)
  have hR_bound := R.height_bound t ht_ne P hP
  -- Suffices to show every prime q ⊊ P∩S is zero (then height(P∩S) ≤ 1)
  change (Ideal.comap S_sub.subtype P).height ≤ ↑(1 : ℕ)
  rw [Ideal.height_le_iff]
  intro q hq_prime hq_lt
  suffices hq_bot : q = ⊥ by rw [hq_bot, Ideal.height_bot]
                             norm_cast
  by_contra hq_ne
  have ⟨s, hs_q, hs_ne⟩ : ∃ s : S_sub, s ∈ q ∧ s ≠ 0 := by
    by_contra h
    push Not at h
    exact hq_ne ((Submodule.eq_bot_iff q).mpr fun x hx => h x hx)
  have ⟨x, hx_PS, hx_nq⟩ := Set.exists_of_ssubset hq_lt
  have hs_carrier : (s : T) ∈ S_carrier := hS_sub_eq' ▸ s.2
  obtain ⟨as, bs, has_Rbar, hbs_Rbar, hbs_nM, hsb_eq⟩ := hs_carrier
  have hx_carrier : (x : T) ∈ S_carrier := hS_sub_eq' ▸ x.2
  obtain ⟨ax, bx, hax_Rbar, hbx_Rbar, hbx_nM, hxb_eq⟩ := hx_carrier
  have hP_le_M : P ≤ IsLocalRing.maximalIdeal T := by
    intro x hx
    by_contra hxnM
    exact hP_prime.ne_top (P.eq_top_of_isUnit_mem hx (IsLocalRing.notMem_maximalIdeal.mp hxnM))
  have heval_x₁_Rbar : ∀ f : Polynomial R.carrier, (aeval x₁ f : T) ∈ Rbar := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]
                       exact hRbar_add _ _ hf hg
    | monomial n r =>
      rw [Polynomial.aeval_monomial]
      change (algebraMap R.carrier T r) * x₁ ^ n ∈ Rbar
      exact hRbar_mul _ _ (R_le_intersectionSet R x₁ x₂ y₁ y₂ r) (by
        induction n with
        | zero => simp only [pow_zero]
                  exact hRbar_one
        | succ n ih => rw [pow_succ]
                       exact hRbar_mul _ _ ih hx₁_Rbar)
  have heval_x₁_S : ∀ f : Polynomial R.carrier, (aeval x₁ f : T) ∈ S_sub :=
    fun f => hRbar_le_S _ (heval_x₁_Rbar f)
  have heval_x₂_Rbar : ∀ f : Polynomial R.carrier, (aeval x₂ f : T) ∈ Rbar := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]
                       exact hRbar_add _ _ hf hg
    | monomial n r =>
      rw [Polynomial.aeval_monomial]
      change (algebraMap R.carrier T r) * x₂ ^ n ∈ Rbar
      exact hRbar_mul _ _ (R_le_intersectionSet R x₁ x₂ y₁ y₂ r) (by
        induction n with
        | zero => simp only [pow_zero]
                  exact hRbar_one
        | succ n ih => rw [pow_succ]
                       exact hRbar_mul _ _ ih hx₂_Rbar)
  have heval_x₂_S : ∀ f : Polynomial R.carrier, (aeval x₂ f : T) ∈ S_sub :=
    fun f => hRbar_le_S _ (heval_x₂_Rbar f)
  -- Coprimality of y₁, y₂: at least one of them avoids P
  have hy_or : (↑y₁ : T) ∉ P ∨ (↑y₂ : T) ∉ P := by
    by_cases hPR : Ideal.comap R.carrier.subtype P = ⊥
    · left
      intro h
      have : y₁ ∈ Ideal.comap R.carrier.subtype P := h
      rw [hPR] at this
      have := Ideal.mem_bot.mp this
      exact hy₁ (congrArg Subtype.val this)
    · exact coprime_not_both_in_prime R y₁ y₂ hcoprime P hR_bound hPR
  -- Reduce to a single branch: work with whichever xᵢ has yⱼ ∉ P
  suffices branch : ∀ (x_eval : T) (y_elem : R.carrier)
      (hy_nP : (↑y_elem : T) ∉ P)
      (hx_ker_branch : ∀ (P' : Ideal T), P'.IsPrime → P' ≠ ⊤ → P'.height ≤ 1 →
        (↑y_elem : T) ∉ P' →
        ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P' →
        ∀ (f : Polynomial R.carrier),
          aeval x_eval f ∈ P' → (C p : Polynomial R.carrier) ∣ f)
      (heval_S : ∀ f : Polynomial R.carrier, (aeval x_eval f : T) ∈ S_sub)
      (hx_trans_branch : Transcendental R.carrier x_eval)
      (get_witness_s : ∃ (f : Polynomial R.carrier) (n : ℕ),
        as * (↑y_elem : T) ^ n = aeval x_eval f)
      (get_witness_x : ∃ (f : Polynomial R.carrier) (n : ℕ),
        ax * (↑y_elem : T) ^ n = aeval x_eval f)
      (hy_ne : (↑y_elem : T) ≠ 0)
      (get_witness_Rbar : ∀ t, t ∈ Rbar →
        ∃ (f : Polynomial R.carrier) (n : ℕ),
          t * (↑y_elem : T) ^ n = aeval x_eval f),
      False by
    rcases hy_or with hy₁_nP | hy₂_nP
    · exact branch x₂ y₁ hy₁_nP hx₂_ker heval_x₂_S hx₂_trans has_Rbar.2 hax_Rbar.2
        hy₁ (fun t ht => ht.2)
    · exact branch x₁ y₂ hy₂_nP hx₁_ker heval_x₁_S hx₁_trans has_Rbar.1 hax_Rbar.1
        hy₂ (fun t ht => ht.1)
  intro x_eval y_elem hy_nP hx_ker_branch heval_S hx_trans_branch
    ⟨fs, ns, hfs⟩ ⟨fx, nx, hfx⟩ hy_ne get_witness_Rbar
  -- Define the evaluation map φ: R[X] → S sending X ↦ x_eval
  let φ : Polynomial R.carrier →+* S_sub :=
    (aeval (R := R.carrier) (A := T) x_eval).toRingHom.codRestrict
      S_sub.toSubsemiring heval_S
  have hφ_val : ∀ f, (φ f : T) = aeval x_eval f := fun _ => rfl
  have hφ_inj : Function.Injective φ := by
    intro f g hfg
    exact (transcendental_iff_injective.mp hx_trans_branch) (congrArg Subtype.val hfg)
  -- Pull back primes to R[X]: J = φ⁻¹(P∩S) and J_q = φ⁻¹(q) with J_q < J
  set J := Ideal.comap φ (Ideal.comap S_sub.subtype P)
  set J_q := Ideal.comap φ q
  haveI hJ_prime : J.IsPrime := (hP_prime.comap S_sub.subtype).comap _
  haveI hJ_q_prime : J_q.IsPrime := hq_prime.comap _
  have hJJ_q : J_q ≤ J := fun f hf => hq_lt.le hf
  have hs_P : (s : T) ∈ P := hq_lt.le hs_q
  have has_P : as ∈ P := hsb_eq ▸ P.mul_mem_right _ hs_P
  have hbs_S : bs ∈ S_sub := hRbar_le_S _ hbs_Rbar
  have hy_S : (↑y_elem : T) ∈ S_sub := hR_le y_elem.2
  have hyn_S : (↑y_elem : T) ^ ns ∈ S_sub := S_sub.pow_mem hy_S ns
  have hbsyn_S : bs * (↑y_elem : T) ^ ns ∈ S_sub := S_sub.mul_mem hbs_S hyn_S
  have hφfs_eq : φ fs = s * ⟨bs * (↑y_elem : T) ^ ns, hbsyn_S⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_mul, hφ_val]
    rw [← hfs, ← hsb_eq]
    ring
  have hfs_q : fs ∈ J_q := show φ fs ∈ q by
    rw [hφfs_eq]
    exact q.mul_mem_right _ hs_q
  have hfs_ne : fs ≠ 0 := by
    intro h
    rw [h, map_zero] at hfs
    have has_ne : as ≠ 0 := by
      intro has0
      have : (↑s : T) * bs = 0 := by rw [hsb_eq, has0]
      rcases mul_eq_zero.mp this with hs0 | hbs0
      · exact hs_ne (Subtype.ext hs0)
      · exact IsUnit.ne_zero (IsLocalRing.notMem_maximalIdeal.mp hbs_nM) hbs0
    exact has_ne ((mul_eq_zero.mp hfs).resolve_right (pow_ne_zero _ hy_ne))
  have hJ_q_ne : J_q ≠ ⊥ := by
    intro h
    rw [h] at hfs_q
    exact hfs_ne (by simpa using hfs_q)
  have hx_P' : (x : T) ∈ P := hx_PS
  have hax_P : ax ∈ P := hxb_eq ▸ P.mul_mem_right _ hx_P'
  have hfx_J : fx ∈ J := show (φ fx : T) ∈ P by
    rw [hφ_val]
    exact hfx ▸ P.mul_mem_right _ hax_P
  have hbx_S : bx ∈ S_sub := hRbar_le_S _ hbx_Rbar
  have hynx_S : (↑y_elem : T) ^ nx ∈ S_sub := S_sub.pow_mem hy_S nx
  have hbxynx_S : bx * (↑y_elem : T) ^ nx ∈ S_sub := S_sub.mul_mem hbx_S hynx_S
  have hφfx_eq : φ fx = x * ⟨bx * (↑y_elem : T) ^ nx, hbxynx_S⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_mul, hφ_val]
    rw [← hfx, ← hxb_eq]
    ring
  -- fx ∈ J but fx ∉ J_q, so J_q ⊊ J strictly
  have hfx_nq : fx ∉ J_q := by
    intro hfx_q
    have h := show φ fx ∈ q from hfx_q
    rw [hφfx_eq] at h
    rcases hq_prime.mem_or_mem h with hx_q | hbxy_q
    · exact hx_nq hx_q
    · have hbxy_P : bx * (↑y_elem : T) ^ nx ∈ P := hq_lt.le hbxy_q
      have hbx_nP : bx ∉ P := fun h => hbx_nM (hP_le_M h)
      have hyn_P : (↑y_elem : T) ^ nx ∈ P :=
        (hP_prime.mem_or_mem hbxy_P).resolve_left hbx_nP
      exact hy_nP (hP_prime.mem_of_pow_mem nx hyn_P)
  have hJJ_strict : J_q < J := lt_of_le_of_ne hJJ_q (fun h => hfx_nq (h ▸ hfx_J))
  -- Case split: P∩R = ⊥ (use K[X] PID argument) vs P∩R ≠ ⊥ (use wf descent)
  by_cases hPR_bot : Ideal.comap R.carrier.subtype P = ⊥
  · have hJ_const_zero : ∀ (c : R.carrier), Polynomial.C c ∈ J → c = 0 := by
      intro c hc
      have hcP : (c : T) ∈ P := by
        have h : (φ (Polynomial.C c) : T) ∈ P := hc
        rwa [hφ_val, Polynomial.aeval_C] at h
      have : c ∈ Ideal.comap R.carrier.subtype P := hcP
      rw [hPR_bot] at this
      exact Ideal.mem_bot.mp this
    have hJ_q_const_zero : ∀ (c : R.carrier), Polynomial.C c ∈ J_q → c = 0 :=
      fun c hc => hJ_const_zero c (hJJ_q hc)
    -- Localize R[X] → K[X]; K[X] is a PID so dim ≤ 1
    set K := FractionRing R.carrier
    set ψ := Polynomial.mapRingHom (algebraMap R.carrier K)
    have hψ_inj : Function.Injective ψ :=
      Polynomial.map_injective _ (IsFractionRing.injective R.carrier K)
    set M' := Submonoid.map (Polynomial.C : R.carrier →+* _) (nonZeroDivisors R.carrier)
    have hJ_disj : Disjoint (M' : Set (Polynomial R.carrier)) (J : Set _) := by
      rw [Set.disjoint_left]
      intro f hfM hfJ
      obtain ⟨c, hc_nzd, rfl⟩ := hfM
      exact (nonZeroDivisors.ne_zero hc_nzd) (hJ_const_zero c hfJ)
    have hJ_q_disj : Disjoint (M' : Set (Polynomial R.carrier)) (J_q : Set _) := by
      rw [Set.disjoint_left]
      intro f hfM hfJ
      obtain ⟨c, hc_nzd, rfl⟩ := hfM
      exact (nonZeroDivisors.ne_zero hc_nzd) (hJ_q_const_zero c hfJ)
    letI : Algebra (Polynomial R.carrier) (Polynomial K) := ψ.toAlgebra
    haveI : IsLocalization M' (Polynomial K) :=
      Polynomial.isLocalization (nonZeroDivisors R.carrier) K
    haveI : (Ideal.map (algebraMap _ (Polynomial K)) J).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M' (Polynomial K) J hJ_prime hJ_disj
    haveI : (Ideal.map (algebraMap _ (Polynomial K)) J_q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint
        M' (Polynomial K) J_q hJ_q_prime hJ_q_disj
    have hJ_q_map_ne :
        Ideal.map (algebraMap _ (Polynomial K)) J_q ≠ ⊥ := by
      intro h
      have hsat := IsLocalization.under_map_of_isPrime_disjoint
        M' (Polynomial K) hJ_q_prime hJ_q_disj
      rw [h] at hsat
      have hbot : Ideal.under (Polynomial R.carrier) (⊥ : Ideal (Polynomial K)) = ⊥ := by
        simpa [Ideal.under_def] using
          Ideal.comap_bot_of_injective (algebraMap (Polynomial R.carrier) (Polynomial K)) hψ_inj
      rw [hbot] at hsat
      exact hJ_q_ne hsat.symm
    haveI : Ring.DimensionLEOne (Polynomial K) :=
      Ring.DimensionLEOne.principal_ideal_ring _
    -- In the PID K[X], two nonzero primes with J_q ≤ J forces J_q = J
    have hmap_eq : Ideal.map (algebraMap _ (Polynomial K)) J_q =
        Ideal.map (algebraMap _ (Polynomial K)) J :=
      (Ring.DimensionLeOne.prime_le_prime_iff_eq hJ_q_map_ne).mp
        (Ideal.map_mono hJJ_q)
    -- Saturating back gives J_q = J, contradicting J_q ⊊ J
    have hJ_sat := IsLocalization.under_map_of_isPrime_disjoint
      M' (Polynomial K) hJ_prime hJ_disj
    have hJ_q_sat := IsLocalization.under_map_of_isPrime_disjoint
      M' (Polynomial K) hJ_q_prime hJ_q_disj
    exact absurd (hJ_q_sat.symm.trans (hmap_eq ▸ hJ_sat))
      (ne_of_lt hJJ_strict)
  -- P∩R ≠ ⊥ case: apply the well-founded descent to get a contradiction
  · exact absurd hs_ne (height_bound_wf_descent R x₁ x₂ y₁ y₂ S_sub hR_le hRbar_le_S hinv
        hR_prime_in_S (fun s => hS_mem_rep s) P hP_ht hR_bound hPR_bot hP_le_M
        x_eval y_elem hy_nP hx_ker_branch heval_S
        get_witness_Rbar q hq_lt s hs_ne hs_q).elim
⟩

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
include T in theorem build_height_bound
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier)
    (S_sub : Subring T) [UniqueFactorizationMonoid S_sub]
    (hR_le : R.carrier ≤ S_sub)
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hx₁_trans : Transcendental R.carrier x₁)
    (hx₂_trans : Transcendental R.carrier x₂)
    (hx₁_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₂ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₁ f ∈ P → (C p : Polynomial R.carrier) ∣ f)
    (hx₂_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₁ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₂ f ∈ P → (C p : Polynomial R.carrier) ∣ f)
    (hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (hR_prime_in_S : ∀ (p : R.carrier), Prime p →
      (↑p : T) ∈ IsLocalRing.maximalIdeal T →
      Prime (⟨(↑p : T), hR_le p.2⟩ : S_sub))
    (hS_sub_eq : (S_sub : Set T) =
      {t : T | ∃ (a : T) (b : T),
        a ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a})
    (hRbar_le_S : ∀ t, t ∈ intersectionSet R x₁ x₂ y₁ y₂ → t ∈ (S_sub : Set T))
    (hx₁_Rbar : x₁ ∈ intersectionSet R x₁ x₂ y₁ y₂)
    (hx₂_Rbar : x₂ ∈ intersectionSet R x₁ x₂ y₁ y₂) :
    ∀ (t : T), t ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
        Ideal.height (P.comap S_sub.subtype) ≤ 1 := by
  exact
    (build_height_bound_proof
      R x₁ x₂ y₁ y₂ S_sub hR_le hcoprime hy₁ hy₂ hAss_ht hM_not_assoc hx₁_trans hx₂_trans
      hx₁_ker hx₂_ker hinv hR_prime_in_S hS_sub_eq hRbar_le_S hx₁_Rbar hx₂_Rbar
    ).down
/-- Helper: the Krull domain intersection construction produces an NSubring
containing both x₁ and x₂. Core algebraic construction from Heitmann (1993) Lemma 4. -/
private def build_intersection_nsubring_proof
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) (c : R.carrier)
    (hc_eq : (↑c : T) = x₁ * ↑y₁ + x₂ * ↑y₂)
    (hx₁_trans : Transcendental R.carrier x₁)
    (hx₂_trans : Transcendental R.carrier x₂)
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (_hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (_hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (_hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hx₁_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₂ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₁ f ∈ P → (C p : Polynomial R.carrier) ∣ f)
    (hx₂_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₁ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₂ f ∈ P → (C p : Polynomial R.carrier) ∣ f) : PLift (
    ∃ S : NSubring T, IsAExtension R S ∧ x₁ ∈ S.carrier ∧ x₂ ∈ S.carrier ) := ⟨by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  -- Derive mod-principal transcendence for both x₁ (mod y₂) and x₂ (mod y₁)
  have hx₁_mod_trans := derive_mod_principal_trans R x₁ y₂ hAss_ht hx₁_ker
  have hx₂_mod_trans := derive_mod_principal_trans R x₂ y₁ hAss_ht hx₂_ker
  set Rbar := intersectionSet R x₁ x₂ y₁ y₂
  have hunit : ∀ (a : T), a ∉ IsLocalRing.maximalIdeal T → IsUnit a :=
    fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha
  have hprod_notmem : ∀ (a b : T),
      a ∉ IsLocalRing.maximalIdeal T → b ∉ IsLocalRing.maximalIdeal T →
      a * b ∉ IsLocalRing.maximalIdeal T := by
    intro a b ha hb
    exact IsLocalRing.notMem_maximalIdeal.mpr ((hunit a ha).mul (hunit b hb))
  -- S = {a/b : a,b ∈ Rbar, b ∉ M} -- localize Rbar at elements outside the maximal ideal
  set S_carrier : Set T :=
    {t : T | ∃ (a : T) (b : T), a ∈ Rbar ∧ b ∈ Rbar ∧
      b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a}
  have hALS_zero : ∀ (x' : T) (y' : R.carrier), (0 : T) ∈ adjoinLocSetY R x' y' :=
    fun x' y' => ⟨0, 0, by simp⟩
  have hALS_one : ∀ (x' : T) (y' : R.carrier), (1 : T) ∈ adjoinLocSetY R x' y' :=
    fun x' y' => ⟨C 1, 0, by simp⟩
  have hALS_neg : ∀ (x' : T) (y' : R.carrier) (t : T),
      t ∈ adjoinLocSetY R x' y' → -t ∈ adjoinLocSetY R x' y' := by
    intro x' y' t ⟨f, n, hf⟩
    exact ⟨-f, n, by rw [map_neg, ← hf, neg_mul]⟩
  have hALS_mul : ∀ (x' : T) (y' : R.carrier) (t₁ t₂ : T),
      t₁ ∈ adjoinLocSetY R x' y' → t₂ ∈ adjoinLocSetY R x' y' →
      t₁ * t₂ ∈ adjoinLocSetY R x' y' := by
    intro x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩
    exact ⟨f₁ * f₂, n₁ + n₂, by
      rw [map_mul, ← hf₁, ← hf₂, pow_add]
      ring⟩
  have hALS_add : ∀ (x' : T) (y' : R.carrier) (t₁ t₂ : T),
      t₁ ∈ adjoinLocSetY R x' y' → t₂ ∈ adjoinLocSetY R x' y' →
      t₁ + t₂ ∈ adjoinLocSetY R x' y' := by
    intro x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩
    refine ⟨f₁ * C (y' ^ n₂) + f₂ * C (y' ^ n₁), n₁ + n₂, ?_⟩
    have key : (t₁ + t₂) * (↑y' : T) ^ (n₁ + n₂) =
        t₁ * (↑y' : T) ^ n₁ * (↑y' : T) ^ n₂ +
        t₂ * (↑y' : T) ^ n₂ * (↑y' : T) ^ n₁ := by
      rw [pow_add]
      ring
    rw [key, hf₁, hf₂, map_add, map_mul, map_mul, aeval_C, aeval_C]
    simp only [show algebraMap R.carrier T = R.carrier.subtype from rfl,
      Subring.coe_subtype, map_pow]
  have hRbar_zero : (0 : T) ∈ Rbar := ⟨hALS_zero x₁ y₂, hALS_zero x₂ y₁⟩
  have hRbar_one : (1 : T) ∈ Rbar := ⟨hALS_one x₁ y₂, hALS_one x₂ y₁⟩
  have hRbar_neg : ∀ t, t ∈ Rbar → -t ∈ Rbar :=
    fun t ⟨h₁, h₂⟩ => ⟨hALS_neg x₁ y₂ t h₁, hALS_neg x₂ y₁ t h₂⟩
  have hRbar_mul : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ * t₂ ∈ Rbar :=
    fun t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩ =>
      ⟨hALS_mul x₁ y₂ t₁ t₂ h₁₁ h₂₁, hALS_mul x₂ y₁ t₁ t₂ h₁₂ h₂₂⟩
  have hRbar_add : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ + t₂ ∈ Rbar :=
    fun t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩ =>
      ⟨hALS_add x₁ y₂ t₁ t₂ h₁₁ h₂₁, hALS_add x₂ y₁ t₁ t₂ h₁₂ h₂₂⟩
  -- Verify S_carrier is closed under ring operations, hence forms a subring of T
  have hS_carrier_subring : ∃ S_sub : Subring T, (S_sub : Set T) = S_carrier := by
    refine ⟨{
      carrier := S_carrier
      zero_mem' := ⟨0, 1, hRbar_zero, hRbar_one,
        IsLocalRing.notMem_maximalIdeal.mpr isUnit_one, by rw [zero_mul]⟩
      one_mem' := ⟨1, 1, hRbar_one, hRbar_one,
        IsLocalRing.notMem_maximalIdeal.mpr isUnit_one, by rw [one_mul]⟩
      neg_mem' := ?neg
      add_mem' := ?add
      mul_mem' := ?mul
    }, rfl⟩
    case neg =>
      intro t ⟨a, b, ha, hb, hb_notM, htb⟩
      exact ⟨-a, b, hRbar_neg a ha, hb, hb_notM, by rw [neg_mul, htb]⟩
    case mul =>
      intro t₁ t₂ ⟨a₁, b₁, ha₁, hb₁, hb₁_notM, ht₁⟩ ⟨a₂, b₂, ha₂, hb₂, hb₂_notM, ht₂⟩
      refine ⟨a₁ * a₂, b₁ * b₂, hRbar_mul a₁ a₂ ha₁ ha₂, hRbar_mul b₁ b₂ hb₁ hb₂,
        hprod_notmem b₁ b₂ hb₁_notM hb₂_notM, ?_⟩
      rw [show t₁ * t₂ * (b₁ * b₂) = (t₁ * b₁) * (t₂ * b₂) from by ring, ht₁, ht₂]
    case add =>
      intro t₁ t₂ ⟨a₁, b₁, ha₁, hb₁, hb₁_notM, ht₁⟩ ⟨a₂, b₂, ha₂, hb₂, hb₂_notM, ht₂⟩
      refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂,
        hRbar_add _ _ (hRbar_mul a₁ b₂ ha₁ hb₂) (hRbar_mul a₂ b₁ ha₂ hb₁),
        hRbar_mul b₁ b₂ hb₁ hb₂,
        hprod_notmem b₁ b₂ hb₁_notM hb₂_notM, ?_⟩
      rw [show (t₁ + t₂) * (b₁ * b₂) = t₁ * b₁ * b₂ + t₂ * b₂ * b₁ from by ring, ht₁, ht₂]
  obtain ⟨S_sub, hS_sub_eq⟩ := hS_carrier_subring
  have hRbar_le_S : ∀ t ∈ Rbar, t ∈ (S_sub : Set T) := by
    intro t ht
    rw [hS_sub_eq]
    exact ⟨t, 1,
      ht,
      ⟨R_le_adjoinLocSetY R x₁ y₂ 1, R_le_adjoinLocSetY R x₂ y₁ 1⟩,
      IsLocalRing.notMem_maximalIdeal.mpr isUnit_one,
      mul_one t⟩
  have hR_le : R.carrier ≤ S_sub := by
    intro r hr
    exact hRbar_le_S _ (R_le_intersectionSet R x₁ x₂ y₁ y₂ ⟨r, hr⟩)
  -- Show x₁ ∈ Rbar: trivially in R[x₁,y₂⁻¹]; in R[x₂,y₁⁻¹] via c = x₁y₁ + x₂y₂
  have hx₁_A₁ : x₁ ∈ adjoinLocSetY R x₁ y₂ := x_mem_adjoinLocSetY R x₁ y₂
  have hx₁_A₂ : x₁ ∈ adjoinLocSetY R x₂ y₁ := by
    refine ⟨C c - X * C y₂, 1, ?_⟩
    rw [pow_one]
    rw [Polynomial.aeval_def, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
    have hc' : x₁ * (↑y₁ : T) = (↑c : T) - x₂ * (↑y₂ : T) := by
      have h := hc_eq
      rw [h]
      ring
    convert hc'
  have hx₁_Rbar : x₁ ∈ Rbar := ⟨hx₁_A₁, hx₁_A₂⟩
  -- Symmetrically, x₂ ∈ Rbar using x₂ = (c - x₁y₁)/y₂
  have hx₂_A₂ : x₂ ∈ adjoinLocSetY R x₂ y₁ := x_mem_adjoinLocSetY R x₂ y₁
  have hx₂_A₁ : x₂ ∈ adjoinLocSetY R x₁ y₂ := by
    refine ⟨C c - X * C y₁, 1, ?_⟩
    rw [pow_one]
    have haeval : (aeval x₁ (C c - X * C y₁) : T) = (↑c : T) - x₁ * (↑y₁ : T) := by
      simp [aeval_def, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X,
        show algebraMap R.carrier T = R.carrier.subtype from rfl]
      ring
    rw [haeval]
    have hc' : x₂ * (↑y₂ : T) = (↑c : T) - x₁ * (↑y₁ : T) := by
      have h := hc_eq
      rw [h]
      ring
    convert hc'
  have hx₂_Rbar : x₂ ∈ Rbar := ⟨hx₂_A₁, hx₂_A₂⟩
  have hx₁_S : x₁ ∈ S_sub := hRbar_le_S _ hx₁_Rbar
  have hx₂_S : x₂ ∈ S_sub := hRbar_le_S _ hx₂_Rbar
  -- S is local: elements outside M are units (their inverses lie in S via the a/b representation)
  have hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s := by
    intro ⟨s, hs_mem⟩ hs_notM
    have hs_carrier : s ∈ S_carrier := by rw [← hS_sub_eq]
                                          exact hs_mem
    obtain ⟨a, b, ha_Rbar, hb_Rbar, hb_notM, hsb_eq⟩ := hs_carrier
    have hs_unit : IsUnit s := hunit s hs_notM
    let s_inv : T := ↑(hs_unit.unit⁻¹ : Tˣ)
    have hs_mul_inv : s * s_inv = 1 := hs_unit.mul_val_inv
    have hs_inv_mul : s_inv * s = 1 := hs_unit.val_inv_mul
    have ha_notM : a ∉ IsLocalRing.maximalIdeal T := by
      rw [← hsb_eq]
      exact hprod_notmem s b hs_notM hb_notM
    have hs_inv_carrier : s_inv ∈ S_carrier := by
      refine ⟨b, a, hb_Rbar, ha_Rbar, ha_notM, ?_⟩
      calc s_inv * a = s_inv * (s * b) := by rw [hsb_eq]
        _ = (s_inv * s) * b := by ring
        _ = 1 * b := by rw [hs_inv_mul]
        _ = b := one_mul b
    have hs_inv_S : s_inv ∈ S_sub := by
      change s_inv ∈ (S_sub : Set T)
      rw [hS_sub_eq]
      exact hs_inv_carrier
    have hmul_one : (⟨s, hs_mem⟩ : S_sub) * ⟨s_inv, hs_inv_S⟩ = 1 :=
      Subtype.ext hs_mul_inv
    exact IsUnit.of_mul_eq_one _ hmul_one
  have hLocal : IsLocalRing S_sub := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    by_cases ham : (a : T) ∈ IsLocalRing.maximalIdeal T
    · right
      apply hinv
      intro h
      have h1 : (1 : T) ∈ IsLocalRing.maximalIdeal T := by
        have h_add := (IsLocalRing.maximalIdeal T).add_mem h ham
        have : (↑(1 - a) : T) + (↑a : T) = 1 := by
          simp [sub_add_cancel]
        rw [this] at h_add
        exact h_add
      exact (IsLocalRing.maximalIdeal T).ne_top_iff_one.mp
        (IsLocalRing.maximalIdeal.isMaximal T).ne_top h1
    · left
      exact hinv a ham
  -- WfDvdMonoid for S: divisibility in S embeds into divisibility in T (which is Noetherian)
  haveI : IsDomain S_sub := inferInstance
  haveI : WfDvdMonoid S_sub := by
    constructor
    apply Subrelation.wf (r := InvImage DvdNotUnit (fun (a : S_sub) => (a : T)))
    · intro a b ⟨ha_ne, c, hc_nu, hab_eq⟩
      refine ⟨fun h => ha_ne (Subtype.ext h), c.val, ?_, congrArg Subtype.val hab_eq⟩
      exact fun hcu_T => hc_nu (hinv c (IsLocalRing.notMem_maximalIdeal.mpr hcu_T))
    · exact InvImage.wf _ IsWellFounded.wf
  have hS_mem_rep : ∀ s : S_sub,
      ∃ (a b : T), a ∈ Rbar ∧ b ∈ Rbar ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ (s : T) * b = a := by
    intro s
    have := s.2
    change s.1 ∈ (S_sub : Set T) at this
    rw [hS_sub_eq] at this
    exact this
  have hRbar_inv_S : ∀ t : T, t ∈ Rbar → t ∉ IsLocalRing.maximalIdeal T →
      ∃ (t_inv : T), t_inv ∈ (S_sub : Set T) ∧ t * t_inv = 1 := by
    intro t ht ht_notM
    have ht_unit := hunit t ht_notM
    refine ⟨↑ht_unit.unit⁻¹, ?_, ht_unit.mul_val_inv⟩
    rw [hS_sub_eq]
    refine ⟨1, t, hRbar_one, ht, ht_notM, ?_⟩
    rw [ht_unit.val_inv_mul]
  -- Rbar is closed under division by primes of R (key for building the UFD structure)
  have hR_prime_div_Rbar : ∀ (p : R.carrier), Prime p → ∀ t ∈ Rbar,
      ∀ (d : T), t = (↑p : T) * d → d ∈ Rbar := by
    intro p hp t ⟨ht_A1, ht_A2⟩ d htpd
    have hcop := hcoprime p hp
    push Not at hcop
    constructor
    · obtain ⟨f, n, hfn⟩ := ht_A1
      have hpd_eq : (↑p : T) * (d * (↑y₂ : T) ^ n) = aeval x₁ f := by
        rw [← hfn, htpd]
        ring
      -- If p | y₂, absorb extra y₂ into the polynomial; otherwise use mod-principal transcendence
      by_cases hpy₂ : p ∣ y₂
      · obtain ⟨q, hq⟩ := hpy₂
        have hy₂_eq : (↑y₂ : T) = (↑p : T) * (↑q : T) := by
          rw [hq]
          simp
        refine ⟨f * C q, n + 1, ?_⟩
        have key : d * (↑y₂ : T) ^ (n + 1) = aeval x₁ f * (↑q : T) := by
          have hpow : (↑y₂ : T) ^ (n + 1) = (↑y₂ : T) ^ n * ((↑p : T) * (↑q : T)) := by
            rw [pow_succ, hy₂_eq]
          rw [hpow]
          have : d * ((↑y₂ : T) ^ n * ((↑p : T) * (↑q : T))) =
              ((↑p : T) * (d * (↑y₂ : T) ^ n)) * (↑q : T) := by ring
          rw [this, hpd_eq]
        rw [key, map_mul, aeval_C,
          show algebraMap R.carrier T = R.carrier.subtype from rfl, Subring.coe_subtype]
      · suffices hCp_dvd : (C p : Polynomial R.carrier) ∣ f by
          obtain ⟨g, hfg⟩ := hCp_dvd
          have hr_ne : (↑p : T) ≠ 0 :=
            fun h => hp.ne_zero (R.carrier.subtype_injective h)
          refine ⟨g, n, mul_left_cancel₀ hr_ne ?_⟩
          rw [hpd_eq, hfg, map_mul, aeval_C,
            show algebraMap R.carrier T = R.carrier.subtype from rfl]
          rfl
        exact hx₁_mod_trans p hp hpy₂ f
          (Ideal.mem_span_singleton.mpr ⟨d * (↑y₂ : T) ^ n, hpd_eq.symm⟩)
    · obtain ⟨f, n, hfn⟩ := ht_A2
      have hpd_eq : (↑p : T) * (d * (↑y₁ : T) ^ n) = aeval x₂ f := by
        rw [← hfn, htpd]
        ring
      by_cases hpy₁ : p ∣ y₁
      · obtain ⟨q, hq⟩ := hpy₁
        have hy₁_eq : (↑y₁ : T) = (↑p : T) * (↑q : T) := by
          rw [hq]
          simp
        refine ⟨f * C q, n + 1, ?_⟩
        have key : d * (↑y₁ : T) ^ (n + 1) = aeval x₂ f * (↑q : T) := by
          have hpow : (↑y₁ : T) ^ (n + 1) = (↑y₁ : T) ^ n * ((↑p : T) * (↑q : T)) := by
            rw [pow_succ, hy₁_eq]
          rw [hpow]
          have : d * ((↑y₁ : T) ^ n * ((↑p : T) * (↑q : T))) =
              ((↑p : T) * (d * (↑y₁ : T) ^ n)) * (↑q : T) := by ring
          rw [this, hpd_eq]
        rw [key, map_mul, aeval_C,
          show algebraMap R.carrier T = R.carrier.subtype from rfl, Subring.coe_subtype]
      · suffices hCp_dvd : (C p : Polynomial R.carrier) ∣ f by
          obtain ⟨g, hfg⟩ := hCp_dvd
          have hr_ne : (↑p : T) ≠ 0 :=
            fun h => hp.ne_zero (R.carrier.subtype_injective h)
          refine ⟨g, n, mul_left_cancel₀ hr_ne ?_⟩
          rw [hpd_eq, hfg, map_mul, aeval_C,
            show algebraMap R.carrier T = R.carrier.subtype from rfl]
          rfl
        exact hx₂_mod_trans p hp hpy₁ f
          (Ideal.mem_span_singleton.mpr ⟨d * (↑y₁ : T) ^ n, hpd_eq.symm⟩)
  -- Primes of R remain prime in S, then build UFD structure on S
  have hR_prime_in_S := build_R_prime_in_S R x₁ x₂ y₁ y₂ S_sub
    hR_le hx₁_trans hx₂_trans hcoprime hS_sub_eq hR_prime_div_Rbar hinv
  have hUFD : UniqueFactorizationMonoid S_sub :=
    build_ufd_proof R x₁ x₂ y₁ y₂ S_sub hR_le hcoprime hy₁ hy₂ hx₁_trans hx₂_trans
      hx₁_mod_trans hx₂_mod_trans hinv hR_prime_in_S hS_sub_eq hRbar_le_S hx₁_Rbar hx₂_Rbar
  -- Cardinality bound: |S| ≤ |Rbar|² ≤ max(aleph0, |R|) since S ↪ Rbar × Rbar via (a,b)
  have hCard_S : Cardinal.mk S_sub ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier) := by
    have hALS_card : Cardinal.mk ↥(adjoinLocSetY R x₁ y₂) ≤
        max Cardinal.aleph0 (Cardinal.mk R.carrier) := by
      have hsub : (adjoinLocSetY R x₁ y₂ : Set T) ⊆
          ⋃ (f : Polynomial R.carrier), {t : T | ∃ n : ℕ, t * (↑y₂ : T) ^ n = aeval x₁ f} := by
        intro t ⟨f, n, h⟩
        exact Set.mem_iUnion.mpr ⟨f, ⟨n, h⟩⟩
      apply le_trans (Cardinal.mk_le_mk_of_subset hsub)
      apply le_trans (Cardinal.mk_iUnion_le _)
      calc Cardinal.mk (Polynomial R.carrier) *
            ⨆ (f : Polynomial R.carrier), Cardinal.mk ↑{t : T | ∃ n : ℕ,
              t * (↑y₂ : T) ^ n = aeval x₁ f}
          ≤ max (Cardinal.mk R.carrier) Cardinal.aleph0 * Cardinal.aleph0 := by
            gcongr
            · exact Polynomial.cardinalMk_le_max
            · apply ciSup_le'
              intro f
              apply Cardinal.mk_le_aleph0_iff.mpr
              apply Set.Countable.to_subtype
              apply (Set.countable_iUnion (fun (n : ℕ) =>
                Set.Subsingleton.countable (fun (t₁ : T) (ht₁ : t₁ * (↑y₂ : T) ^ n = aeval x₁ f)
                  (t₂ : T) (ht₂ : t₂ * (↑y₂ : T) ^ n = aeval x₁ f) =>
                  mul_right_cancel₀ (pow_ne_zero n hy₂) (ht₁.trans ht₂.symm)))).mono
              intro t ⟨n, hn⟩
              exact Set.mem_iUnion.mpr ⟨n, hn⟩
        _ = max (Cardinal.mk R.carrier) Cardinal.aleph0 :=
            Cardinal.mul_aleph0_eq (le_max_right _ _)
        _ = max Cardinal.aleph0 (Cardinal.mk R.carrier) := max_comm _ _
    have hRbar_card : Cardinal.mk ↥Rbar ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier) :=
      le_trans (Cardinal.mk_le_of_injective
        (Set.inclusion_injective (Set.inter_subset_left))) hALS_card
    have hf : Function.Injective (fun (s : S_sub) =>
        Prod.mk
          (⟨(hS_sub_eq ▸ s.2 : s.val ∈ S_carrier).choose,
            (hS_sub_eq ▸ s.2 : s.val ∈ S_carrier).choose_spec.choose_spec.1⟩ : ↥Rbar)
          (⟨(hS_sub_eq ▸ s.2 : s.val ∈ S_carrier).choose_spec.choose,
            (hS_sub_eq ▸ s.2 : s.val ∈ S_carrier).choose_spec.choose_spec.2.1⟩ : ↥Rbar)) := by
      intro s₁ s₂ heq
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at heq
      obtain ⟨ha_eq, hb_eq⟩ := heq
      have h₁ := (hS_sub_eq ▸ s₁.2 : s₁.val ∈ S_carrier).choose_spec.choose_spec
      have h₂ := (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose_spec.choose_spec
      have key : s₁.val * (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose_spec.choose =
                 s₂.val * (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose_spec.choose := by
        calc s₁.val * (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose_spec.choose
            = s₁.val * (hS_sub_eq ▸ s₁.2 : s₁.val ∈ S_carrier).choose_spec.choose := by rw [← hb_eq]
          _ = (hS_sub_eq ▸ s₁.2 : s₁.val ∈ S_carrier).choose := h₁.2.2.2
          _ = (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose := ha_eq
          _ = s₂.val * (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose_spec.choose := h₂.2.2.2.symm
      have hb_ne : (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose_spec.choose ≠ (0 : T) := by
        intro hb0
        exact h₂.2.2.1 (hb0 ▸ Ideal.zero_mem _)
      have hsub : (s₁.val - s₂.val) *
          (hS_sub_eq ▸ s₂.2 : s₂.val ∈ S_carrier).choose_spec.choose = 0 := by
        rw [sub_mul, key, sub_self]
      exact Subtype.ext (sub_eq_zero.mp
        ((mul_eq_zero.mp hsub).resolve_right hb_ne))
    calc Cardinal.mk S_sub
        ≤ Cardinal.mk (↥Rbar × ↥Rbar) := Cardinal.mk_le_of_injective hf
      _ = Cardinal.mk ↥Rbar * Cardinal.mk ↥Rbar := (Cardinal.mul_def _ _).symm
      _ ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier) *
            max Cardinal.aleph0 (Cardinal.mk R.carrier) :=
          mul_le_mul' hRbar_card hRbar_card
      _ = max Cardinal.aleph0 (Cardinal.mk R.carrier) :=
          Cardinal.mul_eq_self (le_max_left _ _)
  have hcard : Cardinal.mk S_sub ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) := by
    calc Cardinal.mk S_sub
        ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier) := hCard_S
      _ ≤ max Cardinal.aleph0 (max Cardinal.aleph0
            (Cardinal.mk (IsLocalRing.ResidueField T))) :=
        by gcongr
           exact R.card_le
      _ = max Cardinal.aleph0
            (Cardinal.mk (IsLocalRing.ResidueField T)) := by simp
  -- The maximal ideal of S is exactly M∩S (S is local with the inherited maximal ideal)
  have hmax_eq : IsLocalRing.maximalIdeal S_sub =
      (IsLocalRing.maximalIdeal T).comap S_sub.subtype := by
    ext ⟨a, ha⟩
    constructor
    · intro hx
      rw [Ideal.mem_comap]
      by_contra h
      rw [IsLocalRing.mem_maximalIdeal] at hx
      exact hx (hinv ⟨a, ha⟩ (show (⟨a, ha⟩ : S_sub).val ∉ IsLocalRing.maximalIdeal T from h))
    · intro hx
      rw [Ideal.mem_comap] at hx
      rw [IsLocalRing.mem_maximalIdeal]
      exact fun hu => (IsLocalRing.mem_maximalIdeal _).mp hx (hu.map S_sub.subtype)
  -- Apply the main height bound theorem to get the Krull domain property for S
  have hheight : ∀ (t : T), t ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
        Ideal.height (P.comap S_sub.subtype) ≤ 1 :=
    build_height_bound R x₁ x₂ y₁ y₂ S_sub hR_le hcoprime hy₁ hy₂ hAss_ht hM_not_assoc
      hx₁_trans hx₂_trans hx₁_ker hx₂_ker hinv hR_prime_in_S hS_sub_eq hRbar_le_S
      hx₁_Rbar hx₂_Rbar
  -- Assemble S into an NSubring and verify it is an A-extension of R
  refine ⟨⟨S_sub, hUFD, hLocal, hcard, hmax_eq, hheight⟩, ?_, hx₁_S, hx₂_S⟩
  exact {
    le := hR_le
    primes_preserved := by
      haveI := hUFD
      exact build_primes_preserved R x₁ x₂ y₁ y₂ S_sub hR_le hx₁_trans hx₂_trans hcoprime
        hmax_eq hS_sub_eq hR_prime_div_Rbar
    card_le := hCard_S
  }
⟩

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
include T in theorem build_intersection_nsubring
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier) (c : R.carrier)
    (hc_eq : (↑c : T) = x₁ * ↑y₁ + x₂ * ↑y₂)
    (hx₁_trans : Transcendental R.carrier x₁)
    (hx₂_trans : Transcendental R.carrier x₂)
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (_hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (_hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (_hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hx₁_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₂ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₁ f ∈ P → (C p : Polynomial R.carrier) ∣ f)
    (hx₂_ker : ∀ (P : Ideal T), P.IsPrime → P ≠ ⊤ → P.height ≤ 1 → (↑y₁ : T) ∉ P →
      ∀ (p : R.carrier), Prime p → (↑p : T) ∈ P →
      ∀ (f : Polynomial R.carrier),
        aeval x₂ f ∈ P → (C p : Polynomial R.carrier) ∣ f) :
    ∃ S : NSubring T, IsAExtension R S ∧ x₁ ∈ S.carrier ∧ x₂ ∈ S.carrier := by
  exact
    (build_intersection_nsubring_proof
      R x₁ x₂ y₁ y₂ c hc_eq hx₁_trans hx₂_trans hcoprime hy₁ hy₂ _hM_ne_bot hM_not_assoc
      hAss_ht _hR_card _hT_card hx₁_ker hx₂_ker
    ).down
end MainTheorem

end
