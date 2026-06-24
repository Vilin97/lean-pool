/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.NSubring
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Order.BourbakiWitt
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Transcendental Extension of N-subrings

Adjoining a transcendental element to an N-subring R of a complete
local domain T and localising at the intersection with the maximal
ideal yields a new N-subring.

Loepp, "Constructing local generic formal fibers", 1997, Lemma 11.
-/


noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Localization Carrier

The subring R[x]_{R[x] ∩ M} inside T, consisting of fractions p(x)/q(x)
where q(x) is a unit in T (equivalently, q(x) ∉ M).
-/

/-- The carrier set of R[x] localized at R[x] ∩ M, viewed inside T.
An element t ∈ T is in this set iff t = p(x)/q(x) for some p,q ∈ R[X]
with q(x) a unit in T (i.e., q(x) ∉ M). -/
def adjoinLocSet (R : NSubring T) (x : T) : Set T :=
  { t : T | ∃ (p q : Polynomial R.carrier),
    (aeval x q : T) ∉ IsLocalRing.maximalIdeal T ∧
    t * (aeval x q : T) = (aeval x p : T) }

/-- The carrier set forms a subring of T. -/
lemma adjoinLocSet_subring (R : NSubring T) (x : T) :
    ∃ (S : Subring T), (S : Set T) = adjoinLocSet R x := by
  have hunit : ∀ (a : T), a ∉ IsLocalRing.maximalIdeal T → IsUnit a :=
    fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha
  have hprod_notmem : ∀ (a b : T),
      a ∉ IsLocalRing.maximalIdeal T → b ∉ IsLocalRing.maximalIdeal T →
      a * b ∉ IsLocalRing.maximalIdeal T := by
    intro a b ha hb
    exact IsLocalRing.notMem_maximalIdeal.mpr ((hunit a ha).mul (hunit b hb))
  refine ⟨{
    carrier := adjoinLocSet R x
    zero_mem' := ⟨0, 1, by rw [map_one]
                           exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one,
      by rw [map_one, mul_one, map_zero]⟩
    one_mem' := ⟨1, 1, by rw [map_one]
                          exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one,
      by rw [map_one, mul_one]⟩
    neg_mem' := ?neg
    add_mem' := ?add
    mul_mem' := ?mul
  }, rfl⟩
  case neg =>
    intro t ⟨p, q, hq, h⟩
    exact ⟨-p, q, hq, by rw [map_neg, ← h, neg_mul]⟩
  case mul =>
    intro t₁ t₂ ⟨p₁, q₁, hq₁, h₁⟩ ⟨p₂, q₂, hq₂, h₂⟩
    refine ⟨p₁ * p₂, q₁ * q₂, ?_, ?_⟩
    · rw [map_mul]
      exact hprod_notmem _ _ hq₁ hq₂
    · rw [map_mul, map_mul, ← h₁, ← h₂]
      ring
  case add =>
    intro t₁ t₂ ⟨p₁, q₁, hq₁, h₁⟩ ⟨p₂, q₂, hq₂, h₂⟩
    refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, ?_, ?_⟩
    · rw [map_mul]
      exact hprod_notmem _ _ hq₁ hq₂
    · rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]
      ring

/-- R.carrier ≤ adjoinLocSet carrier -/
lemma adjoinLocSet_le (R : NSubring T) (x : T)
    (t : T) (ht : t ∈ (R.carrier : Set T)) : t ∈ adjoinLocSet R x := by
  refine ⟨Polynomial.C ⟨t, ht⟩, 1, ?_, ?_⟩
  · rw [map_one]
    exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one
  · rw [map_one, mul_one, aeval_C]
    rfl

/-- x ∈ adjoinLocSet carrier -/
lemma adjoinLocSet_mem_x (R : NSubring T) (x : T) :
    x ∈ adjoinLocSet R x := by
  refine ⟨Polynomial.X, 1, ?_, ?_⟩
  · rw [map_one]
    exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one
  · rw [map_one, mul_one, aeval_X]

/-!
## Transcendental Extension (Loepp Lemma 11)

If x ∈ T is transcendental over Frac(R) and avoids a suitable set of primes,
then R[x] localized at M is again an N-subring.
-/

lemma adjoin_height_case_bot
    (R : NSubring T)
    (x : T)
    (hx_trans : Transcendental R.carrier x)
    (S_sub : Subring T)
    (hS_eq : (S_sub : Set T) = adjoinLocSet R x)
    (hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (P : Ideal T) (hP_prime : P.IsPrime)
    (hPR : P.comap R.carrier.subtype = ⊥) :
    (Ideal.comap S_sub.subtype P).height ≤ ↑(1 : ℕ) := by
  rw [Ideal.height_le_iff]
  intro q hq_prime hq_lt
  suffices q = ⊥ by rw [this, Ideal.height_bot]
                    norm_cast
  by_contra hq_ne
  obtain ⟨s, hs_q, hs_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq_ne
  obtain ⟨x', hx_P, hx_nq⟩ := Set.exists_of_ssubset hq_lt
  have eval_mem' : ∀ f : Polynomial R.carrier, (aeval x f : T) ∈ S_sub := by
    intro f
    change _ ∈ (S_sub : Set T)
    rw [hS_eq]
    exact ⟨f, 1, by rw [map_one]
                    exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one,
      by rw [map_one, mul_one]⟩
  let φ : Polynomial R.carrier →+* S_sub :=
    (aeval (R := R.carrier) (A := T) x).toRingHom.codRestrict
      S_sub.toSubsemiring eval_mem'
  have hφ_val : ∀ f, (φ f : T) = aeval x f := fun _ => rfl
  have hφ_inj : Function.Injective φ := by
    intro f g hfg
    exact (transcendental_iff_injective.mp hx_trans) (congrArg Subtype.val hfg)
  set J := Ideal.comap φ q
  set J' := Ideal.comap φ (Ideal.comap S_sub.subtype P)
  haveI hJ_prime : J.IsPrime := hq_prime.comap _
  haveI hJ'_prime : J'.IsPrime := (hP_prime.comap S_sub.subtype).comap _
  have hJJ' : J ≤ J' := fun f hf => hq_lt.le hf
  obtain ⟨ps, qs, hqs, heqs⟩ : (s : T) ∈ adjoinLocSet R x := hS_eq ▸ s.2
  have hps_J : ps ∈ J := show φ ps ∈ q from by
    have : s * ⟨aeval x qs, eval_mem' qs⟩ = φ ps := Subtype.ext heqs
    rw [← this]
    exact q.mul_mem_right _ hs_q
  have hps_ne : ps ≠ 0 := by
    intro h
    rw [h, map_zero] at heqs
    exact hs_ne (Subtype.ext ((mul_eq_zero.mp heqs).resolve_right
      (IsUnit.ne_zero (IsLocalRing.notMem_maximalIdeal.mp hqs))))
  have hJ_ne : J ≠ ⊥ := by
    intro h
    rw [h] at hps_J
    simp only [Ideal.mem_bot] at hps_J
    exact hps_ne hps_J
  have hJJ'_ne : J ≠ J' := by
    intro heq
    apply hx_nq
    obtain ⟨px', qx', hqx', heqx'⟩ : (x' : T) ∈ adjoinLocSet R x :=
      hS_eq ▸ x'.2
    have hpx'_J' : px' ∈ J' := by
      change (φ px' : T) ∈ P
      rw [hφ_val, ← heqx']
      exact P.mul_mem_right _ (hx_P : (x' : T) ∈ P)
    have hpx'_q : φ px' ∈ q := by
      change px' ∈ J
      rw [heq]
      exact hpx'_J'
    have hmul_q : x' * ⟨aeval x qx', eval_mem' qx'⟩ ∈ q :=
      (Subtype.ext heqx' : x' * ⟨aeval x qx', eval_mem' qx'⟩ = φ px') ▸
        hpx'_q
    exact (hq_prime.mem_or_mem hmul_q).resolve_right
      (fun h => hq_prime.ne_top (Ideal.eq_top_of_isUnit_mem q h (hinv _ hqx')))
  have hJJ'_strict : J < J' := lt_of_le_of_ne hJJ' hJJ'_ne
  have hJ_const_zero : ∀ (c : R.carrier), Polynomial.C c ∈ J → c = 0 := by
    intro c hc
    have hcq := (show φ (Polynomial.C c) ∈ q from hc)
    have hcval : S_sub.subtype (φ (Polynomial.C c)) = (c : T) := by
      change (aeval x (Polynomial.C c) : T) = c
      simp [Polynomial.aeval_C, Algebra.algebraMap_ofSubring]
    have hcP : (c : T) ∈ P := hcval ▸ (hq_lt.le hcq : S_sub.subtype (φ _) ∈ P)
    have := (show c ∈ Ideal.comap R.carrier.subtype P from hcP)
    rw [hPR] at this
    exact Ideal.mem_bot.mp this
  -- Map J, J' to K[X] (PID, dim ≤ 1) to get contradiction via saturation
  set K := FractionRing R.carrier
  set ψ := Polynomial.mapRingHom (algebraMap R.carrier K)
  have hψ_inj : Function.Injective ψ :=
    Polynomial.map_injective _ (IsFractionRing.injective R.carrier K)
  set M' := Submonoid.map (Polynomial.C : R.carrier →+* _) (nonZeroDivisors R.carrier)
  have hJ'_const_zero : ∀ (c : R.carrier), Polynomial.C c ∈ J' → c = 0 := by
    intro c hc
    have : (φ (Polynomial.C c) : T) ∈ P := hc
    have hcval : (φ (Polynomial.C c) : T) = (c : T) := by
      simp [hφ_val, Polynomial.aeval_C, Algebra.algebraMap_ofSubring]
    have hcP : (c : T) ∈ P := hcval ▸ this
    have := (show c ∈ Ideal.comap R.carrier.subtype P from hcP)
    rw [hPR] at this
    exact Ideal.mem_bot.mp this
  have hJ_disj : Disjoint (M' : Set (Polynomial R.carrier)) (J : Set _) := by
    rw [Set.disjoint_left]
    intro f hfM hfJ
    obtain ⟨c, hc_nzd, rfl⟩ := hfM
    exact (nonZeroDivisors.ne_zero hc_nzd) (hJ_const_zero c hfJ)
  have hJ'_disj : Disjoint (M' : Set (Polynomial R.carrier)) (J' : Set _) := by
    rw [Set.disjoint_left]
    intro f hfM hfJ'
    obtain ⟨c, hc_nzd, rfl⟩ := hfM
    exact (nonZeroDivisors.ne_zero hc_nzd) (hJ'_const_zero c hfJ')
  letI : Algebra (Polynomial R.carrier) (Polynomial K) := ψ.toAlgebra
  haveI : IsLocalization M' (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R.carrier) K
  haveI : (Ideal.map (algebraMap _ (Polynomial K)) J).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M' (Polynomial K) J hJ_prime hJ_disj
  haveI : (Ideal.map (algebraMap _ (Polynomial K)) J').IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M' (Polynomial K) J' hJ'_prime hJ'_disj
  have hJ_map_ne : Ideal.map (algebraMap _ (Polynomial K)) J ≠ ⊥ := by
    intro h
    have hsat := IsLocalization.under_map_of_isPrime_disjoint M' (Polynomial K) hJ_prime hJ_disj
    rw [h] at hsat
    have : Ideal.under (Polynomial R.carrier) (⊥ : Ideal (Polynomial K)) = ⊥ := by
      simpa [Ideal.under_def] using
        Ideal.comap_bot_of_injective (algebraMap (Polynomial R.carrier) (Polynomial K)) hψ_inj
    rw [this] at hsat
    exact hJ_ne hsat.symm
  -- K[X] is a PID, dim ≤ 1: nonzero prime ≤ prime implies equality
  have hmap_eq : Ideal.map (algebraMap _ (Polynomial K)) J =
      Ideal.map (algebraMap _ (Polynomial K)) J' :=
    have : Ring.DimensionLEOne (Polynomial K) :=
      Ring.DimensionLEOne.principal_ideal_ring _
    (Ring.DimensionLeOne.prime_le_prime_iff_eq hJ_map_ne).mp (Ideal.map_mono hJJ')
  have hJ_sat := IsLocalization.under_map_of_isPrime_disjoint
    M' (Polynomial K) hJ_prime hJ_disj
  have hJ'_sat := IsLocalization.under_map_of_isPrime_disjoint
    M' (Polynomial K) hJ'_prime hJ'_disj
  exact absurd (hJ_sat.symm.trans (hmap_eq ▸ hJ'_sat)) hJJ'_ne

lemma adjoin_height_case_ne_bot
    (R : NSubring T)
    (x : T)
    (hx_ker : ∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
        P.comap R.carrier.subtype ≠ ⊥ →
        ∀ (f : Polynomial R.carrier),
          (aeval x f : T) ∈ (P : Set T) →
          ∀ i, f.coeff i ∈ P.comap R.carrier.subtype)
    (S_sub : Subring T)
    (hS_eq : (S_sub : Set T) = adjoinLocSet R x)
    (P : Ideal T) (hP_prime : P.IsPrime)
    (hP_ht : P.height ≤ 1)
    (hR_bound : (P.comap R.carrier.subtype).height ≤ 1)
    (hPR : P.comap R.carrier.subtype ≠ ⊥) :
    (Ideal.comap S_sub.subtype P).height ≤ ↑(1 : ℕ) := by
  -- Step 1: Extract a prime generator p₀ of P ∩ R
  obtain ⟨a₀, ha₀_mem, ha₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPR
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  obtain ⟨p₀, hp₀_prime_R, hp₀_dvd, hp₀_mem_PR⟩ : ∃ p₀ : R.carrier,
      Prime p₀ ∧ p₀ ∣ a₀ ∧ p₀ ∈ P.comap R.carrier.subtype := by
    obtain ⟨factors, hfp, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_prime_factors a₀ ha₀_ne
    haveI : (P.comap R.carrier.subtype).IsPrime := hP_prime.comap _
    have hprod_in : factors.prod ∈ P.comap R.carrier.subtype := by
      obtain ⟨u, hu⟩ := hassoc
      rw [← hu] at ha₀_mem
      exact ((hP_prime.comap R.carrier.subtype).mem_or_mem ha₀_mem).elim id
        (fun h => absurd
          ((P.comap R.carrier.subtype).eq_top_of_isUnit_mem h u.isUnit)
          (hP_prime.comap R.carrier.subtype).ne_top)
    have hfactor_in_P : ∃ f ∈ factors, f ∈ P.comap R.carrier.subtype := by
      suffices ∀ (m : Multiset R.carrier), (∀ b ∈ m, Prime b) →
          m.prod ∈ P.comap R.carrier.subtype →
          ∃ f ∈ m, f ∈ P.comap R.carrier.subtype from
        this factors hfp hprod_in
      intro m
      induction m using Multiset.induction with
      | empty =>
        intro _ h
        simp only [Multiset.prod_zero] at h
        exact absurd ((P.comap R.carrier.subtype).eq_top_iff_one.mpr h)
          (hP_prime.comap R.carrier.subtype).ne_top
      | cons a s ih =>
        intro hpr hprod
        rw [Multiset.prod_cons] at hprod
        rcases (hP_prime.comap R.carrier.subtype).mem_or_mem hprod with ha | hs
        · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
        · obtain ⟨f, hf, hfP⟩ :=
            ih (fun b hb => hpr b (Multiset.mem_cons_of_mem hb)) hs
          exact ⟨f, Multiset.mem_cons_of_mem hf, hfP⟩
    obtain ⟨f, hf_mem, hf_P⟩ := hfactor_in_P
    exact ⟨f, hfp f hf_mem, dvd_trans (Multiset.dvd_prod hf_mem) hassoc.dvd, hf_P⟩
  have hp₀_ne : p₀ ≠ 0 := hp₀_prime_R.ne_zero
  have hp₀_ne_T : (p₀ : T) ≠ 0 := fun h => hp₀_ne (Subtype.ext h)
  have hp₀_P : (p₀ : T) ∈ P := hp₀_mem_PR
  -- (p₀) = P ∩ R: height ≤ 1 forces P∩R to be generated by any nonzero prime element
  have hPR_eq : P.comap R.carrier.subtype = Ideal.span {p₀} := by
    apply le_antisymm
    · intro r hr
      rw [Ideal.mem_span_singleton]
      by_contra h_not_dvd
      have hspan_lt : Ideal.span {p₀} < P.comap R.carrier.subtype := by
        refine lt_of_le_of_ne (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp₀_mem_PR)) ?_
        intro heq
        exact h_not_dvd (heq ▸ hr |> Ideal.mem_span_singleton.mp)
      haveI : (Ideal.span {p₀}).IsPrime := by
        rw [Ideal.span_singleton_prime (show p₀ ≠ 0 from hp₀_ne)]
        exact hp₀_prime_R
      haveI : (P.comap R.carrier.subtype).IsPrime := hP_prime.comap _
      have hbot_lt_span : (⊥ : Ideal R.carrier) < Ideal.span {p₀} := by
        rw [bot_lt_iff_ne_bot, ne_eq, Ideal.span_singleton_eq_bot]
        exact hp₀_ne
      have h2 : (2 : ℕ∞) ≤ (P.comap R.carrier.subtype).height :=
        calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
          _ ≤ (⊥ : Ideal R.carrier).height + 1 + 1 := by
              gcongr
              exact zero_le
          _ ≤ (Ideal.span {p₀}).height + 1 := by
              gcongr
              exact Ideal.height_add_one_le_of_lt_of_isPrime hbot_lt_span
          _ ≤ (P.comap R.carrier.subtype).height :=
              Ideal.height_add_one_le_of_lt_of_isPrime hspan_lt
      exact not_lt.mpr h2 (by exact_mod_cast hR_bound.trans_lt (by norm_num))
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp₀_mem_PR)
  have hker : ∀ (f : Polynomial R.carrier), (aeval x f : T) ∈ (P : Set T) →
      ∀ i, f.coeff i ∈ P.comap R.carrier.subtype :=
    hx_ker P hP_prime hP_ht hPR
  have hRS_le : R.carrier ≤ S_sub := by
    intro r hr
    change r ∈ (S_sub : Set T)
    rw [hS_eq]
    exact adjoinLocSet_le R x r hr
  have hdiv_p₀ : ∀ (a : S_sub), (a : T) ∈ P →
      ∃ (b : S_sub), (a : T) = (p₀ : T) * (b : T) := by
    intro a ha_P
    obtain ⟨pa, qa, hqa, heqa⟩ : (a : T) ∈ adjoinLocSet R x := hS_eq ▸ a.2
    have hpa_P : (aeval x pa : T) ∈ P := by
      rw [← heqa]
      exact P.mul_mem_right _ ha_P
    have hcoeff_dvd : ∀ i, p₀ ∣ pa.coeff i := by
      intro i
      have := hker pa hpa_P i
      rwa [hPR_eq, Ideal.mem_span_singleton] at this
    obtain ⟨pa', hpa_eq⟩ := (Polynomial.C_dvd_iff_dvd_coeff p₀ pa).mpr hcoeff_dvd
    have heq_eval : (aeval x pa : T) = (p₀ : T) * aeval x pa' := by
      conv_lhs => rw [hpa_eq, map_mul, aeval_C]
      rfl
    have hqa_unit : IsUnit (aeval x qa : T) := IsLocalRing.notMem_maximalIdeal.mp hqa
    obtain ⟨uqa, huqa⟩ := hqa_unit
    have hb_mem : aeval x pa' * ↑uqa⁻¹ ∈ (S_sub : Set T) := hS_eq ▸
      ⟨pa', qa, hqa, by rw [← huqa, mul_assoc, uqa.inv_mul, mul_one]⟩
    refine ⟨⟨aeval x pa' * ↑uqa⁻¹, hb_mem⟩, ?_⟩
    change (a : T) = (p₀ : T) * (aeval x pa' * ↑uqa⁻¹)
    have ha_val : (a : T) = aeval x pa * ↑uqa⁻¹ := by
      calc (a : T) = a * aeval x qa * ↑uqa⁻¹ := by
            rw [← huqa, mul_assoc, uqa.mul_inv, mul_one]
        _ = aeval x pa * ↑uqa⁻¹ := by rw [heqa]
    rw [ha_val, heq_eval]
    ring
  have hp₀_not_unit_T : ¬IsUnit (p₀ : T) :=
    fun hu => hP_prime.ne_top (P.eq_top_of_isUnit_mem hp₀_P hu)
  set p₀_S : S_sub := ⟨(p₀ : T), hRS_le p₀.2⟩
  -- Step 2: Show height(P∩S) ≤ 1 via well-founded descent on divisibility by p₀
  rw [Ideal.height_le_iff]
  intro q hq_prime hq_lt
  suffices q = ⊥ by rw [this, Ideal.height_bot]
                    norm_cast
  by_contra hq_ne
  obtain ⟨s, hs_q, hs_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq_ne
  haveI : q.IsPrime := hq_prime
  have hp₀_not_q : p₀_S ∉ q := by
    intro hp₀q
    have hsub : Ideal.comap S_sub.subtype P ≤ q := by
      intro a ha_PS
      obtain ⟨b, hb_eq⟩ := hdiv_p₀ a ha_PS
      have hab : a = p₀_S * b := Subtype.ext hb_eq
      rw [hab]
      exact Ideal.mul_mem_right b q hp₀q
    exact lt_irrefl q (lt_of_lt_of_le hq_lt hsub)
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
    (hq_prime.mem_or_mem (hab ▸ ha_q)).resolve_left hp₀_not_q
  have hdvd : DvdNotUnit (b : T) w :=
    ⟨hb_ne_T, (p₀ : T), hp₀_not_unit_T, haw.symm.trans (hb_eq.trans (mul_comm _ _))⟩
  exact ha_ne (Subtype.ext (by
    have hb0 := ih (b : T) hdvd b rfl hb_q
    simp [hb_eq, congrArg Subtype.val hb0]))

/-- Elements of the localization carrier outside the maximal ideal are units. -/
private lemma adjoinLoc_isUnit_of_notMem_maximalIdeal
    (R : NSubring T) (x : T) (S_sub : Subring T)
    (hS_eq : (S_sub : Set T) = adjoinLocSet R x) :
    ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s := by
  intro ⟨s, hs⟩ hns
  have hs' : s ∈ adjoinLocSet R x := hS_eq ▸ hs
  obtain ⟨p, q, hq, heq⟩ := hs'
  have hs_unit : IsUnit s := IsLocalRing.notMem_maximalIdeal.mp hns
  obtain ⟨u, rfl⟩ := hs_unit
  have hp : (aeval x p : T) ∉ IsLocalRing.maximalIdeal T := by
    rw [← heq]
    exact IsLocalRing.notMem_maximalIdeal.mpr
      (u.isUnit.mul (IsLocalRing.notMem_maximalIdeal.mp hq))
  have hinv_mem : (↑u⁻¹ : T) ∈ S_sub := by
    change (↑u⁻¹ : T) ∈ (S_sub : Set T)
    rw [hS_eq]
    refine ⟨q, p, hp, ?_⟩
    have : (↑u⁻¹ : T) * ↑u = 1 := by
      rw [← Units.val_mul]
      simp
    rw [← heq]
    ring_nf
    rw [this, one_mul]
  exact IsUnit.of_mul_eq_one (⟨↑u⁻¹, hinv_mem⟩ : S_sub)
    (Subtype.ext (by
                    change (↑u : T) * ↑u⁻¹ = 1
                    rw [← Units.val_mul]
                    simp))

/-- The localization carrier `R[x]_{R[x] ∩ M}` is a unique factorization monoid. -/
private lemma adjoinLoc_uniqueFactorizationMonoid
    (R : NSubring T) (x : T) (hx_trans : Transcendental R.carrier x)
    (S_sub : Subring T) (hS_eq : (S_sub : Set T) = adjoinLocSet R x)
    (hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s) :
    UniqueFactorizationMonoid S_sub := by
  haveI : IsDomain S_sub := inferInstance
  haveI : UniqueFactorizationMonoid (R.carrier)[X] := Polynomial.uniqueFactorizationMonoid
  have eval_mem : ∀ f : (R.carrier)[X], (aeval x f : T) ∈ S_sub := by
    intro f
    change (aeval x f : T) ∈ (S_sub : Set T)
    rw [hS_eq]
    exact ⟨f, 1, by rw [map_one]
                    exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one,
      by rw [map_one, mul_one]⟩
  haveI : WfDvdMonoid S_sub := by
    constructor
    apply Subrelation.wf (r := InvImage DvdNotUnit (fun (a : S_sub) => (a : T)))
    · intro a b ⟨ha_ne, c, hc_nu, hab_eq⟩
      refine ⟨fun h => ha_ne (Subtype.ext h), c.val, ?_, congrArg Subtype.val hab_eq⟩
      exact fun hcu_T => hc_nu (hinv c (IsLocalRing.notMem_maximalIdeal.mpr hcu_T))
    · exact InvImage.wf _ IsWellFounded.wf
  apply UniqueFactorizationMonoid.mk (fun {a} => ⟨fun ha_irr => ?_, Prime.irreducible⟩)
  have ha_M : (a : T) ∈ IsLocalRing.maximalIdeal T := by
    by_contra h
    exact ha_irr.1 (hinv a h)
  obtain ⟨pa, qa, hqa, heqa⟩ : (a : T) ∈ adjoinLocSet R x := hS_eq ▸ a.2
  have hpa_M : (aeval x pa : T) ∈ IsLocalRing.maximalIdeal T := by
    rw [← heqa]
    exact (IsLocalRing.maximalIdeal T).mul_mem_right _ ha_M
  have hpa_ne : pa ≠ 0 := by
    intro h
    rw [h, map_zero] at heqa
    have : (a : T) = 0 := (mul_eq_zero.mp heqa).resolve_right
      (IsUnit.ne_zero (IsLocalRing.notMem_maximalIdeal.mp hqa))
    exact ha_irr.ne_zero (Subtype.ext this)
  -- Find a prime factor f of pa with f(x) ∈ M (if all factors had f(x) ∉ M, pa(x) ∉ M)
  have hfind : ∃ f : (R.carrier)[X], Prime f ∧ f ∣ pa ∧
      (aeval x f : T) ∈ IsLocalRing.maximalIdeal T := by
    obtain ⟨factors, hfp, hassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors pa hpa_ne
    by_contra hall
    push Not at hall
    have hunit : ∀ f ∈ factors, IsUnit (aeval x f : T) := fun f hf =>
      IsLocalRing.notMem_maximalIdeal.mp
        (hall f (hfp f hf) (dvd_trans (Multiset.dvd_prod hf) hassoc.dvd))
    have hprod_unit : IsUnit ((factors.map (fun f => (aeval x f : T))).prod) := by
      refine (factors.map _).prod_induction IsUnit (fun a b => IsUnit.mul) isUnit_one ?_
      intro t ht
      rw [Multiset.mem_map] at ht
      obtain ⟨f, hf, rfl⟩ := ht
      exact hunit f hf
    obtain ⟨u, hu⟩ := hassoc
    have : IsUnit (aeval x pa : T) := by
      rw [← hu, map_mul, map_multiset_prod]
      exact hprod_unit.mul (u.isUnit.map (aeval x))
    exact (IsLocalRing.notMem_maximalIdeal.mpr this) hpa_M
  obtain ⟨f, hf_prime, hf_dvd_pa, hf_M⟩ := hfind
  obtain ⟨g, hfg⟩ := hf_dvd_pa
  have hqa_unit : IsUnit (aeval x qa : T) := IsLocalRing.notMem_maximalIdeal.mp hqa
  obtain ⟨uqa, huqa⟩ := hqa_unit
  have hg_div_qa_mem : aeval x g * ↑uqa⁻¹ ∈ (S_sub : Set T) := hS_eq ▸
    ⟨g, qa, hqa, by rw [← huqa, mul_assoc, uqa.inv_mul, mul_one]⟩
  have ha_eq : (a : T) = aeval x f * (aeval x g * ↑uqa⁻¹) := by
    have : (a : T) * aeval x qa = aeval x f * aeval x g := by rw [heqa, hfg, map_mul]
    calc (a : T) = a * aeval x qa * ↑uqa⁻¹ := by
            rw [← huqa, mul_assoc, uqa.mul_inv, mul_one]
      _ = aeval x f * aeval x g * ↑uqa⁻¹ := by rw [this]
      _ = aeval x f * (aeval x g * ↑uqa⁻¹) := by ring
  have hf_not_unit : ¬ IsUnit (⟨aeval x f, eval_mem f⟩ : S_sub) :=
    fun hu => (IsLocalRing.mem_maximalIdeal _).mp hf_M (hu.map S_sub.subtype)
  have hv_unit : IsUnit (⟨aeval x g * ↑uqa⁻¹, hg_div_qa_mem⟩ : S_sub) := by
    have hdvd : (⟨aeval x f, eval_mem f⟩ : S_sub) ∣ a :=
      ⟨⟨_, hg_div_qa_mem⟩, Subtype.ext ha_eq⟩
    exact (ha_irr.isUnit_or_isUnit (Subtype.ext ha_eq)).resolve_left hf_not_unit
  -- a is associated to f(x); prove a is prime using primality of f in R[X]
  refine ⟨ha_irr.ne_zero, ha_irr.1, ?_⟩
  intro b c ⟨d, hd⟩
  obtain ⟨pb, qb, hqb, heqb⟩ : (b : T) ∈ adjoinLocSet R x := hS_eq ▸ b.2
  obtain ⟨pc, qc, hqc, heqc⟩ : (c : T) ∈ adjoinLocSet R x := hS_eq ▸ c.2
  obtain ⟨pd, qd, hqd, heqd⟩ : (d : T) ∈ adjoinLocSet R x := hS_eq ▸ d.2
  have heq_T : (b : T) * (c : T) = (a : T) * (d : T) := by
    have h := Subtype.ext_iff.mp hd
    simpa using h
  have hinj := transcendental_iff_injective.mp hx_trans
  have poly_eq : pb * pc * qa * qd = pa * pd * qb * qc := by
    apply hinj
    simp only [map_mul]
    calc aeval x pb * aeval x pc * aeval x qa * aeval x qd
        = (↑b * aeval x qb) * (↑c * aeval x qc) * aeval x qa * aeval x qd := by
          rw [heqb, heqc]
      _ = ↑b * ↑c * (aeval x qb * aeval x qc * aeval x qa * aeval x qd) := by ring
      _ = ↑a * ↑d * (aeval x qb * aeval x qc * aeval x qa * aeval x qd) := by rw [heq_T]
      _ = (↑a * aeval x qa) * (↑d * aeval x qd) * aeval x qb * aeval x qc := by ring
      _ = aeval x pa * aeval x pd * aeval x qb * aeval x qc := by rw [heqa, heqd]
  have hf_dvd_rhs : f ∣ pb * pc * qa * qd := by
    have : pa ∣ pb * pc * qa * qd := ⟨pd * qb * qc, by rw [poly_eq]
                                                       ring⟩
    exact dvd_trans ⟨g, hfg⟩ this
  have hf_dvd_rhs' : f ∣ (pb * pc) * (qa * qd) := by
    rw [show (pb * pc) * (qa * qd) = pb * pc * qa * qd from by ring]
    exact hf_dvd_rhs
  have hassoc_fa : Associated (⟨aeval x f, eval_mem f⟩ : S_sub) a :=
    ⟨hv_unit.unit, by rw [IsUnit.unit_spec]
                      exact (Subtype.ext ha_eq).symm⟩
  rcases hf_prime.dvd_or_dvd hf_dvd_rhs' with hf_dvd_bc | hf_dvd_qaqd
  · rcases hf_prime.dvd_or_dvd hf_dvd_bc with hf_dvd_pb | hf_dvd_pc
    · left
      obtain ⟨e, he⟩ := hf_dvd_pb
      have hqb_unit : IsUnit (aeval x qb : T) := IsLocalRing.notMem_maximalIdeal.mp hqb
      obtain ⟨uqb, huqb⟩ := hqb_unit
      have hw_mem : aeval x e * ↑uqb⁻¹ ∈ (S_sub : Set T) := hS_eq ▸
        ⟨e, qb, hqb, by rw [← huqb, mul_assoc, uqb.inv_mul, mul_one]⟩
      have hb_eq : (b : T) = aeval x f * (aeval x e * ↑uqb⁻¹) := by
        calc (b : T) = b * aeval x qb * ↑uqb⁻¹ := by
              rw [← huqb, mul_assoc, uqb.mul_inv, mul_one]
          _ = aeval x pb * ↑uqb⁻¹ := by rw [heqb]
          _ = aeval x f * aeval x e * ↑uqb⁻¹ := by rw [he, map_mul]
          _ = aeval x f * (aeval x e * ↑uqb⁻¹) := by ring
      have hfx_dvd_b : (⟨aeval x f, eval_mem f⟩ : S_sub) ∣ b :=
        ⟨⟨_, hw_mem⟩, Subtype.ext hb_eq⟩
      exact (hassoc_fa.dvd_iff_dvd_left.mp hfx_dvd_b)
    · right
      obtain ⟨e, he⟩ := hf_dvd_pc
      have hqc_unit : IsUnit (aeval x qc : T) := IsLocalRing.notMem_maximalIdeal.mp hqc
      obtain ⟨uqc, huqc⟩ := hqc_unit
      have hw_mem : aeval x e * ↑uqc⁻¹ ∈ (S_sub : Set T) := hS_eq ▸
        ⟨e, qc, hqc, by rw [← huqc, mul_assoc, uqc.inv_mul, mul_one]⟩
      have hc_eq : (c : T) = aeval x f * (aeval x e * ↑uqc⁻¹) := by
        calc (c : T) = c * aeval x qc * ↑uqc⁻¹ := by
              rw [← huqc, mul_assoc, uqc.mul_inv, mul_one]
          _ = aeval x pc * ↑uqc⁻¹ := by rw [heqc]
          _ = aeval x f * aeval x e * ↑uqc⁻¹ := by rw [he, map_mul]
          _ = aeval x f * (aeval x e * ↑uqc⁻¹) := by ring
      have hfx_dvd_c : (⟨aeval x f, eval_mem f⟩ : S_sub) ∣ c :=
        ⟨⟨_, hw_mem⟩, Subtype.ext hc_eq⟩
      exact (hassoc_fa.dvd_iff_dvd_left.mp hfx_dvd_c)
  · -- f | qa * qd contradicts qa(x)*qd(x) ∉ M since f(x) ∈ M
    exfalso
    obtain ⟨w, hw⟩ := hf_dvd_qaqd
    have : (aeval x qa : T) * aeval x qd = aeval x f * aeval x w := by
      rw [← map_mul, ← map_mul, hw]
    have hprod_nM : (aeval x qa : T) * aeval x qd ∉ IsLocalRing.maximalIdeal T :=
      IsLocalRing.notMem_maximalIdeal.mpr
        ((IsLocalRing.notMem_maximalIdeal.mp hqa).mul
          (IsLocalRing.notMem_maximalIdeal.mp hqd))
    exact hprod_nM (this ▸ Ideal.mul_mem_right _ _ hf_M)

/-- Prime elements of `R` remain prime in the localization carrier. -/
private lemma adjoinLoc_prime_of_prime
    (R : NSubring T) (x : T) (hx_trans : Transcendental R.carrier x)
    (S_sub : Subring T) (hS_eq : (S_sub : Set T) = adjoinLocSet R x)
    (hRS : R.carrier ≤ S_sub) :
    ∀ (r : R.carrier), Prime r → Prime (⟨r.1, hRS r.2⟩ : S_sub) := by
  intro r hr
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hr.ne_zero (Subtype.ext (show r.1 = 0 from congrArg Subtype.val h))
  · intro hr_unit
    have hr_not_unit_R : ¬ IsUnit r := hr.not_unit
    have hr_mem_maxR : r ∈ IsLocalRing.maximalIdeal R.carrier :=
      (IsLocalRing.mem_maximalIdeal _).mpr hr_not_unit_R
    have hr_mem_M : r.1 ∈ IsLocalRing.maximalIdeal T := by
      rw [R.maximal_ideal_eq, Ideal.mem_comap] at hr_mem_maxR
      exact hr_mem_maxR
    have hr_not_unit_T : ¬ IsUnit r.1 :=
      (IsLocalRing.mem_maximalIdeal _).mp hr_mem_M
    exact hr_not_unit_T (hr_unit.map S_sub.subtype)
  · intro a b ⟨c, hc⟩
    have ha_mem : (a : T) ∈ adjoinLocSet R x := hS_eq ▸ a.2
    have hb_mem : (b : T) ∈ adjoinLocSet R x := hS_eq ▸ b.2
    have hc_mem : (c : T) ∈ adjoinLocSet R x := hS_eq ▸ c.2
    obtain ⟨pa, qa, hqa, heqa⟩ := ha_mem
    obtain ⟨pb, qb, hqb, heqb⟩ := hb_mem
    obtain ⟨pc, qc, hqc, heqc⟩ := hc_mem
    have heq_T : aeval x pa * aeval x pb * aeval x qc =
        r.1 * aeval x pc * aeval x qa * aeval x qb := by
      have hab : (a : T) * (b : T) = r.1 * (c : T) := by
        have h := Subtype.ext_iff.mp hc
        simpa using h
      calc aeval x pa * aeval x pb * aeval x qc
          = ((a : T) * aeval x qa) * ((b : T) * aeval x qb) * aeval x qc := by
            rw [heqa, heqb]
        _ = (a : T) * (b : T) * (aeval x qa * aeval x qb * aeval x qc) := by ring
        _ = r.1 * (c : T) * (aeval x qa * aeval x qb * aeval x qc) := by rw [hab]
        _ = r.1 * ((c : T) * aeval x qc) * aeval x qa * aeval x qb := by ring
        _ = r.1 * aeval x pc * aeval x qa * aeval x qb := by rw [heqc]
    have hinj := transcendental_iff_injective.mp hx_trans
    have poly_eq : pa * pb * qc = C r * pc * qa * qb := by
      apply hinj
      simp only [map_mul, aeval_C]
      exact heq_T
    have hCr_prime : Prime (C r : (R.carrier)[X]) := Polynomial.prime_C_iff.mpr hr
    have hCr_dvd : C r ∣ pa * pb * qc := ⟨pc * qa * qb, by rw [poly_eq]
                                                           ring⟩
    have hr_mem_M : r.1 ∈ IsLocalRing.maximalIdeal T := by
      have hmem : r ∈ IsLocalRing.maximalIdeal R.carrier :=
        (IsLocalRing.mem_maximalIdeal _).mpr hr.not_unit
      rw [R.maximal_ideal_eq, Ideal.mem_comap] at hmem
      exact hmem
    rcases hCr_prime.dvd_or_dvd
      (show C r ∣ pa * pb * qc from hCr_dvd) with hCr_dvd_papb | hCr_dvd_qc
    · rcases hCr_prime.dvd_or_dvd hCr_dvd_papb with hCr_dvd_pa | hCr_dvd_pb
      · left
        obtain ⟨d, hd⟩ := hCr_dvd_pa
        have heq_pa : (aeval x pa : T) = r.1 * aeval x d := by
          have : aeval x (C r * d) = aeval x pa := by rw [← hd]
          rw [map_mul, aeval_C] at this
          exact this.symm
        have heq_a : (a : T) * aeval x qa = r.1 * aeval x d := by
          rw [heqa, heq_pa]
        have hqa_unit : IsUnit (aeval x qa : T) :=
          IsLocalRing.notMem_maximalIdeal.mp hqa
        have hc'_mem_set : ∃ (c' : T), c' ∈ adjoinLocSet R x ∧
            c' * aeval x qa = aeval x d := by
          obtain ⟨u, hu⟩ := hqa_unit
          refine ⟨aeval x d * ↑u⁻¹, ?_, ?_⟩
          · refine ⟨d, qa, hqa, ?_⟩
            rw [← hu, mul_assoc, u.inv_mul, mul_one]
          · rw [← hu, mul_assoc, u.inv_mul, mul_one]
        obtain ⟨c', hc'_mem, hc'_eq⟩ := hc'_mem_set
        have hc'_S : c' ∈ (S_sub : Set T) := hS_eq ▸ hc'_mem
        have ha_eq : (a : T) = r.1 * c' := by
          have hqa_ne : (aeval x qa : T) ≠ 0 := IsUnit.ne_zero hqa_unit
          have h : (a : T) * aeval x qa = r.1 * c' * aeval x qa := by
            rw [mul_assoc, hc'_eq]
            exact heq_a
          exact mul_right_cancel₀ hqa_ne h
        exact ⟨⟨c', hc'_S⟩, Subtype.ext ha_eq⟩
      · right
        obtain ⟨d, hd⟩ := hCr_dvd_pb
        have heq_pb : (aeval x pb : T) = r.1 * aeval x d := by
          have : aeval x (C r * d) = aeval x pb := by rw [← hd]
          rw [map_mul, aeval_C] at this
          exact this.symm
        have heq_b : (b : T) * aeval x qb = r.1 * aeval x d := by
          rw [heqb, heq_pb]
        have hqb_unit : IsUnit (aeval x qb : T) :=
          IsLocalRing.notMem_maximalIdeal.mp hqb
        obtain ⟨u, hu⟩ := hqb_unit
        have hc'_mem_set : ∃ (c' : T), c' ∈ adjoinLocSet R x ∧
            c' * aeval x qb = aeval x d := by
          refine ⟨aeval x d * ↑u⁻¹, ?_, ?_⟩
          · refine ⟨d, qb, hqb, ?_⟩
            rw [← hu, mul_assoc, u.inv_mul, mul_one]
          · rw [← hu, mul_assoc, Units.inv_mul, mul_one]
        obtain ⟨c', hc'_mem, hc'_eq⟩ := hc'_mem_set
        have hc'_S : c' ∈ (S_sub : Set T) := hS_eq ▸ hc'_mem
        have hb_eq : (b : T) = r.1 * c' := by
          have hqb_ne : (aeval x qb : T) ≠ 0 :=
            IsUnit.ne_zero (IsLocalRing.notMem_maximalIdeal.mp hqb)
          have h : (b : T) * aeval x qb = r.1 * c' * aeval x qb := by
            rw [mul_assoc, hc'_eq]
            exact heq_b
          exact mul_right_cancel₀ hqb_ne h
        exact ⟨⟨c', hc'_S⟩, Subtype.ext hb_eq⟩
    · exfalso
      obtain ⟨d, hd⟩ := hCr_dvd_qc
      have : (aeval x qc : T) = r.1 * aeval x d := by
        have : aeval x (C r * d) = aeval x qc := by rw [← hd]
        simp [map_mul, aeval_C] at this
        exact this.symm
      apply hqc
      rw [this]
      exact Ideal.mul_mem_right (aeval x d) _ hr_mem_M

/-- Loepp Lemma 11 (simplified for P = (0)):
Adjoining a transcendental element to an N-subring yields an N-subring.

If x ∈ T satisfies:
- x ∉ P for all P in a suitable set C ⊇ Ass(T) ∪ {P ∈ Ass(T/rT) | r ∈ R, r ≠ 0}
- x + P is transcendental over R/(R ∩ P) for all P ∈ C
Then S = R[x]_{R[x] ∩ M} is an N-subring with |S| = sup(ℵ₀, |R|). -/
theorem adjoin_transcendental_isNSubring
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (x : T)
    (hx_trans : Transcendental R.carrier x)
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hx_ker : ∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
        P.comap R.carrier.subtype ≠ ⊥ →
        ∀ (f : Polynomial R.carrier),
          (aeval x f : T) ∈ (P : Set T) →
          ∀ i, f.coeff i ∈ P.comap R.carrier.subtype) :
    ∃ S : NSubring T, IsAExtension R S ∧ x ∈ (S.carrier : Set T) := by
  -- Step 1: Obtain the carrier subring S = R[x]_{R[x] ∩ M}
  obtain ⟨S_sub, hS_eq⟩ := adjoinLocSet_subring R x
  have hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s :=
    adjoinLoc_isUnit_of_notMem_maximalIdeal R x S_sub hS_eq
  -- Step 2: S is a local ring
  have hLocal : IsLocalRing S_sub := by
    haveI : Nontrivial S_sub := inferInstance
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro ⟨a, ha⟩
    by_cases ham : (a : T) ∈ IsLocalRing.maximalIdeal T
    · right
      apply hinv
      intro h
      have h1 : (1 : T) ∈ IsLocalRing.maximalIdeal T := by
        have := (IsLocalRing.maximalIdeal T).add_mem h ham
        simp at this
      exact (IsLocalRing.maximalIdeal.isMaximal (R := T)).ne_top
        ((IsLocalRing.maximalIdeal T).eq_top_iff_one.mpr h1)
    · left
      exact hinv ⟨a, ha⟩ ham
  -- Step 3: Cardinality bound via injection S ↪ R[X] × R[X]
  have hCard_S : Cardinal.mk S_sub ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier) := by
    have h_mem : ∀ s : S_sub, (s : T) ∈ adjoinLocSet R x := fun s => hS_eq ▸ s.2
    let f : S_sub → (R.carrier)[X] × (R.carrier)[X] :=
      fun s => ((h_mem s).choose, (h_mem s).choose_spec.choose)
    have hf : Function.Injective f := by
      intro s₁ s₂ heq
      simp only [f, Prod.mk.injEq] at heq
      obtain ⟨hp, hq⟩ := heq
      have heq₁ := (h_mem s₁).choose_spec.choose_spec.2
      have heq₂ := (h_mem s₂).choose_spec.choose_spec.2
      have hq_unit := (h_mem s₁).choose_spec.choose_spec.1
      ext
      apply mul_right_cancel₀ (IsUnit.ne_zero (IsLocalRing.notMem_maximalIdeal.mp hq_unit))
      calc (↑s₁ : T) * aeval x (h_mem s₁).choose_spec.choose
          = aeval x (h_mem s₁).choose := heq₁
        _ = aeval x (h_mem s₂).choose := congrArg (aeval x ·) hp
        _ = (↑s₂ : T) * aeval x (h_mem s₂).choose_spec.choose := heq₂.symm
        _ = (↑s₂ : T) * aeval x (h_mem s₁).choose_spec.choose := by
            congr 1
            exact congrArg (aeval x ·) hq.symm
    calc Cardinal.mk S_sub
        ≤ Cardinal.mk ((R.carrier)[X] × (R.carrier)[X]) := Cardinal.mk_le_of_injective hf
      _ = Cardinal.mk (R.carrier)[X] * Cardinal.mk (R.carrier)[X] :=
          (Cardinal.mul_def _ _).symm
      _ ≤ max (Cardinal.mk R.carrier) Cardinal.aleph0 *
            max (Cardinal.mk R.carrier) Cardinal.aleph0 := by
          gcongr <;> exact Polynomial.cardinalMk_le_max
      _ = max (Cardinal.mk R.carrier) Cardinal.aleph0 :=
          Cardinal.mul_eq_self (le_max_right _ _)
      _ = max Cardinal.aleph0 (Cardinal.mk R.carrier) := max_comm _ _
  have hCard_NSubring : Cardinal.mk S_sub ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) := by
    calc Cardinal.mk S_sub
        ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier) := hCard_S
      _ ≤ max Cardinal.aleph0 (max Cardinal.aleph0
            (Cardinal.mk (IsLocalRing.ResidueField T))) := by
          gcongr
          exact R.card_le
      _ = max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) := by
          simp
  have hMaxIdealEq : IsLocalRing.maximalIdeal S_sub =
      (IsLocalRing.maximalIdeal T).comap S_sub.subtype := by
    ext ⟨a, ha⟩
    constructor
    · intro hx
      rw [Ideal.mem_comap]
      by_contra h
      rw [IsLocalRing.mem_maximalIdeal] at hx
      exact hx (hinv ⟨a, ha⟩
        (show (⟨a, ha⟩ : S_sub).val ∉ IsLocalRing.maximalIdeal T from h))
    · intro hx
      rw [Ideal.mem_comap] at hx
      rw [IsLocalRing.mem_maximalIdeal]
      exact fun hu => (IsLocalRing.mem_maximalIdeal _).mp hx (hu.map S_sub.subtype)
  -- Step 4: S is a UFD (localization of UFD R[x] at prime complement)
  have hUFD : UniqueFactorizationMonoid S_sub :=
    adjoinLoc_uniqueFactorizationMonoid R x hx_trans S_sub hS_eq hinv
  -- Step 5: Height bound - case split on P ∩ R = ⊥ vs ≠ ⊥
  have hHeight : ∀ (t : T), t ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
        Ideal.height (P.comap S_sub.subtype) ≤ 1 := by
    intro t ht_ne P hP
    have hP_prime : P.IsPrime := hP.isPrime
    by_cases hPR : P.comap R.carrier.subtype = ⊥
    · exact adjoin_height_case_bot R x hx_trans S_sub hS_eq hinv P hP_prime hPR
    · exact adjoin_height_case_ne_bot R x hx_ker S_sub hS_eq
        P hP_prime (hAss_ht t ht_ne P hP) (R.height_bound t ht_ne P hP) hPR
  -- Step 6: Assemble the NSubring and verify R ≤ S
  let S_nsub : NSubring T :=
    ⟨S_sub, hUFD, hLocal, hCard_NSubring, hMaxIdealEq, hHeight⟩
  have hRS : R.carrier ≤ S_nsub.carrier := by
    intro r hr
    change r ∈ S_sub
    have : r ∈ adjoinLocSet R x := adjoinLocSet_le R x r hr
    rwa [← hS_eq] at this
  have hprimes : ∀ (r : R.carrier), Prime r →
      Prime (⟨r.1, hRS r.2⟩ : S_nsub.carrier) :=
    adjoinLoc_prime_of_prime R x hx_trans S_sub hS_eq hRS
  refine ⟨S_nsub, ⟨hRS, hprimes, hCard_S⟩, ?_⟩
  change x ∈ (S_sub : Set T)
  have : x ∈ adjoinLocSet R x := adjoinLocSet_mem_x R x
  rwa [← hS_eq] at this


end
