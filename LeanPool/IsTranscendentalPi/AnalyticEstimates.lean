/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
import LeanPool.IsTranscendentalPi.NivenPolynomials
import Mathlib.RingTheory.Int.Basic

/-!
# Analytic estimates

Uniform bounds on the Niven auxiliary polynomials, controlling the size of the
integral appearing in Niven's proof of the transcendence of `π`.
-/

open Polynomial
open Complex

open scoped Polynomial
open scoped BigOperators

noncomputable section

local notation "rexp" => Real.exp

/-- There is a uniform bound `‖Fₚ(t a)‖ ≤ ‖a‖ᵖ⁻¹ Mᵖ` for `0 < t ≤ 1`. -/
lemma Fp_bounded
  (T : ℤ[X]) (a : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℕ, ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖aeval (t * a) (Fp T p)‖ ≤ ‖a‖ ^ (p - 1) * M ^ p := by
  obtain ⟨M, hM⟩ := T_bounded T a
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro p t ht
  simp only [Fp, aeval_mul, map_pow, aeval_X, Complex.norm_mul,
    norm_pow, norm_real, Real.norm_eq_abs]
  rcases ht with ⟨ht0, ht1⟩
  have ht0' : 0 ≤ t := le_of_lt (by simpa using ht0)
  have ht1' : |t| ≤ 1 := by simpa [abs_of_nonneg ht0'] using ht1
  have hmul : |t| * ‖a‖ ≤ ‖a‖ := by
    simpa using mul_le_mul_of_nonneg_right ht1' (norm_nonneg ‖a‖)
  have hpow1 : (|t| * ‖a‖) ^ (p - 1) ≤ ‖a‖ ^ (p - 1) :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hmul _
  have hpow2 : ‖aeval (t * a) T‖ ^ p ≤ (max M 0) ^ p :=
    pow_le_pow_left₀ (norm_nonneg _) ((hM t ⟨ht0, ht1⟩).trans (le_max_left _ _)) _
  exact mul_le_mul hpow1 hpow2 (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _)

/-- There is a uniform bound
`‖a * exp(-(t a)) * Fₚ(t a)‖ ≤ ‖a‖ᵖ * exp(‖a‖) * Mᵖ` for `0 < t ≤ 1`. -/
lemma Fp_cexp_bounded (T : ℤ[X]) (a : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℕ, 0 < p → ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖a * cexp (-(t * a)) * aeval (t * a) (Fp T p)‖ ≤ ‖a‖ ^ p * rexp ‖a‖ * M ^ p := by
  obtain ⟨M, hM0, hFp⟩ := Fp_bounded T a
  refine ⟨M, hM0, ?_⟩
  intro p hp t ht
  have hcexp := norm_cexp_neg_mul_le_exp_norm a t (Set.uIoc_subset_uIcc ht)
  have hfp := hFp p t ht
  have hp' : p = (p - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 hp)).symm
  calc
    ‖a * cexp (-(t * a)) * aeval (t * a) (Fp T p)‖
        = ‖a‖ * ‖cexp (-(t * a))‖ * ‖aeval (t * a) (Fp T p)‖ := by simp [mul_assoc, mul_comm]
    _ ≤ ‖a‖ * rexp ‖a‖ * (‖a‖ ^ (p - 1) * M ^ p) := by gcongr
    _ ≤ (‖a‖ * ‖a‖ ^ (p - 1)) * rexp ‖a‖ * M ^ p :=
          le_of_eq (by simp [mul_assoc, mul_left_comm, mul_comm])
    _ = _ := by rw [hp', pow_succ, Nat.add_sub_cancel, mul_comm ‖a‖ (‖a‖ ^ (p - 1)), ← pow_succ]

/-- The integral ``∫₀¹ a * exp(-(t a)) * T(t a) dt` is `≤ ‖a‖ᵖ * exp(‖a‖) * Mᵖ`. -/
lemma intExpNegPoly_bounded
  (T : ℤ[X]) (a : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℕ, 0 < p → ‖intExpNegPoly (Fp T p) a‖
      ≤ ‖a‖ ^ p * rexp ‖a‖ * M ^ p := by
  obtain ⟨M, hM0, hM⟩ := Fp_cexp_bounded T a
  refine ⟨M, hM0, ?_⟩
  intro p hp
  simpa [intExpNegPoly] using
  (intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ))
    (b := (1 : ℝ))
    (f := fun t : ℝ => a * cexp (-(t * a)) * aeval (t * a) (Fp T p))
    (by
      intro t ht
      simpa [mul_assoc] using hM p hp t ht))

/-- The weighted sum `∑ᵢ bᵢ exp(aᵢ) ∫₀¹ aᵢ * exp(-(t aᵢ)) * T(t aᵢ) dt` is `≤ A Bᵖ`. -/
lemma sum_intExpNegPoly_bound
  (n : ℕ) (T : ℤ[X]) (hn : 0 < n) (a b : Fin n → ℂ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ p : ℕ, 0 < p → ‖∑ i : Fin n, b i * cexp (a i) * intExpNegPoly (Fp T p) (a i)‖
        ≤ A * B ^ p) := by
  have huniv_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, by simp⟩
  choose M hM0 hM using (fun i : Fin n => intExpNegPoly_bounded T (a i))
  let A : ℝ := ∑ i : Fin n, ‖b i * cexp (a i)‖ * rexp ‖a i‖
  let B : ℝ := Finset.sup' Finset.univ huniv_nonempty (fun i : Fin n => ‖a i‖ * M i)
  have hB : ∀ i : Fin n, ‖a i‖ * M i ≤ B := by
    intro i
    simpa [B] using
      (Finset.le_sup' (s := Finset.univ)
        (f := fun j : Fin n => ‖a j‖ * M j) (by simp : i ∈ Finset.univ))
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by
    let i0 : Fin n := ⟨0, hn⟩
    exact le_trans (mul_nonneg (norm_nonneg _) (hM0 i0)) (hB i0)
  refine ⟨A, B, hA0, hB0, ?_⟩
  intro p hp
  have hpow : ∀ i : Fin n, (‖a i‖ * M i) ^ p ≤ B ^ p :=
    fun i => pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (hM0 i)) (hB i) p
  calc
    _ ≤ ∑ i : Fin n, ‖b i * cexp (a i) * intExpNegPoly (Fp T p) (a i)‖ := by
          simpa using (norm_sum_le (Finset.univ)
              (fun i : Fin n => b i * cexp (a i) * intExpNegPoly (Fp T p) (a i)))
    _ ≤ ∑ i : Fin n, ‖b i‖ * ‖cexp (a i)‖ * ‖intExpNegPoly (Fp T p) (a i)‖ := by simp
    _ ≤ ∑ i : Fin n, ‖b i * cexp (a i)‖ * rexp ‖a i‖ * (‖a i‖ * M i) ^ p := by
      refine Finset.sum_le_sum (fun i hi => by
        simpa [mul_assoc, mul_left_comm, mul_pow] using
          (mul_le_mul_of_nonneg_left (hM i p hp) (norm_nonneg (b i * cexp (a i)))))
    _ ≤ ∑ i : Fin n, ‖b i * cexp (a i)‖ * rexp ‖a i‖ * B ^ p :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hpow i) (by positivity))
    _ ≤ _ := le_of_eq (Finset.sum_mul (s := Finset.univ)
                        (f := fun i : Fin n => ‖b i * cexp (a i)‖ * rexp ‖a i‖)
                        (a := B ^ p)).symm

/-- For `p` large, `cᵖ ‖∑ᵢ bᵢ exp(aᵢ) ∫₀¹ aᵢ * exp(-(t aᵢ)) * T(t aᵢ) dt‖` is `≤ (p - 1)!`. -/
lemma sum_intExpNegPoly_asym_ubound
  (n : ℕ) (T : ℤ[X]) (hn : 0 < n) (a b : Fin n → ℂ) (c : ℂ) :
    ∀ᶠ (p : ℕ) in Filter.atTop,
      ‖c ^ p * (∑ i : Fin n, b i * cexp (a i) * intExpNegPoly (Fp T p) (a i))‖
        < (p - 1).factorial := by
  obtain ⟨A, B, hA0, hB0, hAB⟩ := sum_intExpNegPoly_bound n T hn a b
  let a0 : ℕ := ⌈A⌉₊
  let c0 : ℕ := ⌈‖c‖ * B⌉₊
  have hAceil : A ≤ (a0 : ℝ) := Nat.le_ceil A
  have hCceil : ‖c‖ * B ≤ (c0 : ℝ) := Nat.le_ceil (‖c‖ * B)
  have hpos : ∀ᶠ p : ℕ in Filter.atTop, 0 < p := Filter.eventually_gt_atTop 0
  have hfacNat : ∀ᶠ p : ℕ in Filter.atTop, a0 * c0 ^ p < (p - 1).factorial :=
    Nat.eventually_mul_pow_lt_factorial_sub a0 c0 1
  filter_upwards [hpos, hfacNat] with p hp hfacp
  have hfacR : (a0 : ℝ) * (c0 : ℝ) ^ p < (p - 1).factorial := by exact_mod_cast hfacp
  refine lt_of_le_of_lt ?_ hfacR
  calc
    _ = ‖c‖ ^ p * ‖∑ i : Fin n, b i * cexp (a i) * intExpNegPoly (Fp T p) (a i)‖ := by simp
    _ ≤ ‖c‖ ^ p * (A * B ^ p) := by gcongr; exact hAB p hp
    _ = A * (‖c‖ * B) ^ p := by ring_nf
    _ ≤ _ := by gcongr

/-- We have that `F_{p,d}(0) ∑ᵢ₌₀ⁿ⁻¹ bᵢ eᵃⁱ − ∑ᵢ₌₀ⁿ⁻¹ bᵢ F_{p,d}(aᵢ)` can be written as
`((p−1)! T(0)ᵖ + p! Gₚ(0)) ∑ᵢ₌₀ⁿ⁻¹ bᵢ eᵃⁱ − p! ∑ᵢ₌₀ⁿ⁻¹ bᵢ Gₚ(aᵢ)`. -/
lemma sum_cexp_simp
  (n p : ℕ) (T : ℤ[X]) (a b : Fin n → ℂ)
  (hn : 0 < n) (hp : 0 < p)
  (ha : ∀ i : Fin n, a i ≠ 0)
  (hroot : ∀ i : Fin n, a i ∈ T.aroots ℂ) :
    aeval 0 (Fpd T p) * (∑ i : Fin n, b i * cexp (a i))
      - ∑ i : Fin n, b i * aeval (a i) (Fpd T p) =
    ((p - 1).factorial * (aeval (0 : ℂ) T) ^ p
        + p.factorial * aeval (0 : ℂ) (Gp T p))
      * ∑ i : Fin n, b i * cexp (a i)
      - p.factorial * ∑ i : Fin n, b i * aeval (a i) (Gp T p) := by
  rw [aeval_Fpd_at_zero T p hp (TwithRootNotZero T (a ⟨0, hn⟩) (hroot ⟨0, hn⟩))]
  simp_rw [fun i : Fin n => aeval_Fpd_at_nonzero T p (a i) (ha i) (hroot i)]
  simp_rw [factorise_sumIteratedDerivPoly T p, aeval_mul, aeval_C]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by ac_rfl

/-- The sum `∑ᵢ bᵢ exp(aᵢ) ∫₀¹ aᵢ * exp(-(t aᵢ)) * T(t aᵢ) dt`
can be as `((p−1)! T(0)ᵖ + p! Gₚ(0)) ∑ᵢ₌₀ⁿ⁻¹ bᵢ eᵃⁱ − p! ∑ᵢ₌₀ⁿ⁻¹ bᵢ Gₚ(aᵢ)`. -/
lemma intExpNegPoly_eq
    (n p : ℕ) (T : ℤ[X]) (a b : Fin n → ℂ)
    (hn : 0 < n) (hp : 0 < p)
    (ha : ∀ i : Fin n, a i ≠ 0)
    (hroot : ∀ i : Fin n, a i ∈ T.aroots ℂ) :
    ∑ i : Fin n, b i * cexp (a i) * intExpNegPoly (Fp T p) (a i)
      =
      ((((p - 1).factorial * (aeval (0 : ℂ) T) ^ p
          + p.factorial * aeval (0 : ℂ) (Gp T p))
        * ∑ i : Fin n, b i * cexp (a i))
        - p.factorial * ∑ i : Fin n, b i * aeval (a i) (Gp T p)) := by
  rw [intExpNegPoly_sum_simp n p T a b, sum_cexp_simp n p T a b hn hp ha hroot]

/-- If `cᵖ ∑ᵢ₌₀ⁿ⁻¹ bᵢ Gₚ(aᵢ) = f(p) ∈ ℤ`, then
`cᵖ (((p−1)! T(0)ᵖ + p! Gₚ(0)) · (-k) − p! ∑ᵢ₌₀ⁿ⁻¹ bᵢ Gₚ(aᵢ))` is equal to
`− (p−1)! (k cᵖ T(0)ᵖ + p (k cᵖ Gₚ(0) + f(p)))`. -/
lemma sum_cexp_eq
  (n p : ℕ) (T : ℤ[X]) (a b : Fin n → ℂ) (c k : ℤ) (f : ℕ → ℤ) (hp : 0 < p)
  (hfp : c ^ p * (∑ i : Fin n, b i * aeval (a i) (Gp T p)) = f p) :
    c ^ p * (((p - 1).factorial * (aeval (0 : ℂ) T) ^ p
              + p.factorial * aeval (0 : ℂ) (Gp T p)) * (-k)
              - p.factorial * ∑ i : Fin n, b i * aeval (a i) (Gp T p))
      = ((p - 1).factorial *
          -(k * (c ^ p * T.coeff 0 ^ p) + p * (k * (c ^ p * (Gp T p).coeff 0) + f p)) : ℂ) := by
  have hfac : (p.factorial : ℂ) = p * (p - 1).factorial := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hp)).symm
  calc
    _ = ((p - 1).factorial * (c ^ p * (aeval (0 : ℂ) T) ^ p)
            + p.factorial * (c ^ p * aeval (0 : ℂ) (Gp T p))) * (-k)
            - p.factorial * (c ^ p * ∑ i : Fin n, b i * aeval (a i) (Gp T p)) := by ring
    _ = ((p - 1).factorial * (c ^ p * (aeval (0 : ℂ) T) ^ p)
            + p.factorial * (c ^ p * aeval (0 : ℂ) (Gp T p))) * (-k)
            - p.factorial * (f p) := by rw [hfp]
    _ = ((p - 1).factorial * c ^ p * T.coeff 0 ^ p
            + p.factorial * c ^ p * ((Gp T p).coeff 0)) * (-k)
            - p.factorial * (f p) := by simp [aeval_zero_eq_cast_coeff_zero, mul_assoc]
    _ = ((p - 1).factorial * c ^ p * T.coeff 0 ^ p
            + (p * (p - 1).factorial) * c ^ p * ((Gp T p).coeff 0)) * (-k)
            - (p * (p - 1).factorial) * (f p) := by simp [hfac]
    _ = _ := by ring_nf

/-- If `cᵖ ∑ᵢ₌₀ⁿ⁻¹ bᵢ Gₚ(aᵢ) = f(p) ∈ ℤ`, then for sufficiently large primes `p`,
`‖cᵖ (((p−1)! T(0)ᵖ + p! Gₚ(0)) · (-k) − p! ∑ᵢ₌₀ⁿ⁻¹ bᵢ Gₚ(aᵢ))‖ ≥ (p - 1)!`. -/
lemma sum_Gp_asym_lbound
  (n : ℕ) (T : ℤ[X]) (a b : Fin n → ℂ) (c k : ℤ) (f : ℕ → ℤ)
  (hc : c ≠ 0) (hk : k ≠ 0) (hT : aeval (0 : ℂ) T ≠ 0)
  (hf : ∀ᶠ p : {p : ℕ // Nat.Prime p} in Filter.atTop,
    c ^ (p : ℕ) * (∑ i : Fin n, b i * aeval (a i) (Gp T (p : ℕ)))
      = (f (p : ℕ) : ℂ)) :
    ∀ᶠ p : {p : ℕ // Nat.Prime p} in Filter.atTop,
      ‖c ^ (p : ℕ) * ((((p : ℕ) - 1).factorial * (aeval (0 : ℂ) T) ^ (p : ℕ)
        + (p : ℕ).factorial * aeval (0 : ℂ) (Gp T (p : ℕ))) * (-(k))
            - (p : ℕ).factorial * ∑ i : Fin n, b i * aeval (a i) (Gp T (p : ℕ)))‖
        ≥ ((p : ℕ) - 1).factorial := by
  have hkcT0 : k * (c * T.coeff 0) ≠ 0 := by
    simpa [aeval_zero_eq_cast_coeff_zero] using And.intro hk (And.intro hc hT)
  have hnotdvd :
    ∀ᶠ p : {p : ℕ // Nat.Prime p} in Filter.atTop,
      ¬ (p : ℕ) ∣ Int.natAbs (k * (c * T.coeff 0)) := by
    letI : Nonempty {p : ℕ // Nat.Prime p} := ⟨⟨2, by decide⟩⟩
    rcases Nat.exists_infinite_primes (Int.natAbs (k * (c * T.coeff 0)) + 1) with ⟨q, hq, hqprime⟩
    refine Filter.eventually_atTop.2 ⟨⟨q, hqprime⟩, fun p hp => ?_⟩
    exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.2 hkcT0)
      (lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) hq) hp)
  filter_upwards [hf, hnotdvd] with p hpEq hpLarge
  rw [sum_cexp_eq n (p : ℕ) T a b c k f p.2.pos hpEq]
  let z := -(k * (c ^ (p : ℕ) * T.coeff 0 ^ (p : ℕ))
            + ((p : ℕ) : ℤ) * (k * (c ^ (p : ℕ) * (Gp T (p : ℕ)).coeff 0) + f (p : ℕ)))
  have hz : z ≠ 0 := by
    intro hm
    have hdiv : (p : ℕ) ∣ Int.natAbs (k * (c * T.coeff 0)) := by
      apply (Int.ofNat_dvd_left).1
      replace hm := by simpa [z] using neg_eq_zero.mp hm
      rw [← eq_neg_iff_add_eq_zero] at hm
      replace hm : (p : ℤ) ∣ k * (c ^ (p : ℕ) * T.coeff 0 ^ (p : ℕ)) := by simp [hm]
      replace hm : (p : ℤ) ∣ k * (c * T.coeff 0) ^ (p : ℕ) := by simpa [mul_pow] using hm
      rcases Int.Prime.dvd_mul' p.2 hm with hk | hc
      · exact dvd_mul_of_dvd_left hk (c * T.coeff 0)
      · exact dvd_mul_of_dvd_right (Int.Prime.dvd_pow' p.2 hc) k
    exact hpLarge hdiv
  calc
    _ = ‖(((((p : ℕ) - 1).factorial : ℤ) * z : ℤ) : ℂ)‖ := by simp [z]
    _ = (((p : ℕ) - 1).factorial : ℝ) * |(z : ℝ)| := by simp
    _ ≥ (((p : ℕ) - 1).factorial : ℝ) * 1 := by gcongr; exact_mod_cast Int.one_le_abs hz
    _ = _ := by ring
