/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# Nagata's criterion

Let R be an integral domain satisfying ACC on divisibility, and
let p be a prime element such that R[p^{-1}] is a UFD. Then R
is a UFD. The proof uses Kaplansky's theorem: every nonzero
prime ideal of R contains a prime element, obtained by lifting
a prime from the localisation and cancelling powers of p.
-/

noncomputable section

open Cardinal Ideal Set Pointwise

section Nagata

variable {R₀ : Type*} [CommRing R₀] [IsDomain R₀]

theorem nagata_powers_le_nonZeroDivisors (p : R₀) (hp : Prime p) :
    Submonoid.powers p ≤ nonZeroDivisors R₀ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero

theorem nagata_algebraMap_injective (p : R₀) (hp : Prime p) :
    Function.Injective (algebraMap R₀ (Localization.Away p)) :=
  IsLocalization.injective _ (nagata_powers_le_nonZeroDivisors p hp)

/-- Key cancellation lemma: if `p` is prime, `p ∤ q`, and `q ∣ a * p ^ n`,
    then `q ∣ a`. We peel off factors of `p` one at a time. -/
theorem dvd_of_dvd_mul_prime_pow {p q a : R₀} (hp : Prime p) (hpq : ¬p ∣ q) :
    ∀ n : ℕ, q ∣ a * p ^ n → q ∣ a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro h
    apply ih
    rw [pow_succ, ← mul_assoc] at h
    obtain ⟨c, hc⟩ := h
    have hpc : p ∣ c := by
      refine (hp.dvd_or_dvd ?_).resolve_left hpq
      exact ⟨a * p ^ n, by rw [mul_comm p, hc]⟩
    obtain ⟨d, rfl⟩ := hpc
    refine ⟨d, mul_right_cancel₀ hp.ne_zero ?_⟩
    rw [hc, mul_assoc, mul_comm p d, ← mul_assoc]

/-- If `q ∈ R₀` has prime image in `Localization.Away p` and `p ∤ q`,
    then `q` is prime in `R₀`. -/
theorem prime_of_image_prime (p : R₀) (hp : Prime p) (q : R₀)
    (hpq : ¬p ∣ q)
    (hq_loc : Prime (algebraMap R₀ (Localization.Away p) q)) :
    Prime q := by
  -- Lift primality from R[p⁻¹] to R by clearing denominators
  have hinj := nagata_algebraMap_injective p hp
  refine ⟨fun h => by simp [h] at hq_loc,
    fun hu => hq_loc.not_unit (IsUnit.map (algebraMap R₀ (Localization.Away p)) hu),
    fun a b hab => ?_⟩
  have hab' : algebraMap R₀ (Localization.Away p) q ∣
      algebraMap R₀ _ a * algebraMap R₀ _ b := by
    rw [← map_mul]
    exact map_dvd _ hab
  suffices hdvd : ∀ (x : R₀),
      (algebraMap R₀ (Localization.Away p) q ∣ algebraMap R₀ _ x) → q ∣ x by
    exact (hq_loc.dvd_or_dvd hab').imp (hdvd a) (hdvd b)
  intro x hqx
  obtain ⟨z, hz⟩ := hqx
  obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers p) z
  have key : x * p ^ n = q * c := by
    apply hinj
    rw [map_mul, map_mul, map_pow]
    calc algebraMap R₀ _ x * (algebraMap R₀ _ p) ^ n
        = algebraMap R₀ _ q * (z * (algebraMap R₀ _ p) ^ n) := by rw [hz, mul_assoc]
      _ = algebraMap R₀ _ q * algebraMap R₀ _ c := by rw [← map_pow, hc]
  exact dvd_of_dvd_mul_prime_pow hp hpq n ⟨c, key⟩

/-- Nagata's criterion: if p is prime in R and R[p⁻¹] is a UFD, then R is a UFD.
    This is the converse direction of localization preserving UFDs:
    if inverting one prime element yields a UFD, the original ring was already a UFD. -/
theorem nagata_criterion [WfDvdMonoid R₀]
    (p : R₀) (hp : Prime p)
    (hUFD_loc : UniqueFactorizationMonoid (Localization.Away p)) :
    UniqueFactorizationMonoid R₀ := by
  -- By Kaplansky's theorem: show every nonzero prime ideal contains a prime element
  apply UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr
  intro P hPbot hPprime
  by_cases hpP : (p : R₀) ∈ P
  · exact ⟨p, hpP, hp⟩
  -- Case p ∉ P: the image Q of P in R[p⁻¹] is a nonzero prime; extract a prime from Q
  · have hdisj : Disjoint (Submonoid.powers p : Set R₀) (P : Set R₀) := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hxP
      exact hpP (hPprime.mem_of_pow_mem n hxP)
    have hQ_prime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers p) (Localization.Away p) P hPprime hdisj
    have hQ_ne_bot : Ideal.map (algebraMap R₀ (Localization.Away p)) P ≠ ⊥ := by
      intro h
      have hinj := nagata_algebraMap_injective p hp
      refine hPbot (eq_bot_iff.mpr fun x hx => Ideal.mem_bot.mpr ?_)
      have : algebraMap R₀ (Localization.Away p) x ∈ Ideal.map (algebraMap R₀ _) P :=
        Ideal.mem_map_of_mem _ hx
      rw [h, Ideal.mem_bot] at this
      exact hinj (by rw [this, map_zero])
    have : IsDomain (Localization.Away p) :=
      IsLocalization.isDomain_localization (nagata_powers_le_nonZeroDivisors p hp)
    set Q := Ideal.map (algebraMap R₀ (Localization.Away p)) P
    obtain ⟨q', hq'Q, hq'_prime⟩ :=
      (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp hUFD_loc) Q hQ_ne_bot hQ_prime
    obtain ⟨n, r, hq'_eq⟩ := IsLocalization.Away.surj (x := p) q'
    have hr_in_Q : algebraMap R₀ (Localization.Away p) r ∈ Q := by
      rw [← hq'_eq]
      exact Q.mul_mem_right _ hq'Q
    have hr_in_P : r ∈ P := by
      rw [← IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers p) (Localization.Away p) hPprime hdisj]
      exact Ideal.mem_comap.mpr hr_in_Q
    have hr_ne : r ≠ 0 := by
      intro h
      rw [h, map_zero] at hq'_eq
      rcases mul_eq_zero.mp hq'_eq with h1 | h1
      · exact hq'_prime.ne_zero h1
      · exact (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit (R := R₀)
          (S := Localization.Away p) p)).ne_zero h1
    -- Factor out the maximal power of p from r to get r = p^k · r' with p ∤ r'
    obtain ⟨k, r', hpr', hr_eq⟩ := WfDvdMonoid.max_power_factor' hr_ne hp.not_unit
    have hr'_in_P : r' ∈ P := by
      rw [hr_eq] at hr_in_P
      exact (hPprime.mem_or_mem hr_in_P).resolve_left
        (fun h => hpP (hPprime.mem_of_pow_mem k h))
    have hr'_ne : r' ≠ 0 := right_ne_zero_of_mul (hr_eq ▸ hr_ne)
    -- r' is associated to q' in R[p⁻¹], so r' is prime there; lift to R via prime_of_image_prime
    have hr'_prime_loc : Prime (algebraMap R₀ (Localization.Away p) r') := by
      have hpk_unit : IsUnit (algebraMap R₀ (Localization.Away p) (p ^ k)) := by
        rw [map_pow]
        exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit p)
      have hassoc : Associated (algebraMap R₀ (Localization.Away p) r') q' := by
        have h2 : algebraMap R₀ _ (p ^ k) * algebraMap R₀ _ r' =
            q' * (algebraMap R₀ _ p) ^ n := by
          rw [← map_mul, ← hr_eq, hq'_eq]
        have hpn_unit : IsUnit ((algebraMap R₀ (Localization.Away p) p) ^ n) :=
          IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit p)
        exact (associated_unit_mul_right _ _ hpk_unit).trans
          (h2 ▸ associated_mul_unit_left _ _ hpn_unit)
      exact hassoc.prime_iff.mpr hq'_prime
    exact ⟨r', hr'_in_P, prime_of_image_prime p hp r' hpr' hr'_prime_loc⟩

end Nagata

end
