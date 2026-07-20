/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait, Xinze Li
-/

import LeanPool.RamanujanNagell.Helpers

/-!
# The Ramanujan-Nagell equation

The integer ring `R = ℤ[(1 + √-7)/2] = QuadraticAlgebra ℤ (-2) 1` is a Euclidean
domain (see `Helpers.lean`); in particular it is a PID and a UFD. The proof
below uses these facts together with `units_pm_one`, `theta_irreducible`,
`theta'_irreducible`, and the UFD scaffolding `ufd_power_association`.
-/

namespace RamanujanNagell

open Polynomial QuadraticAlgebra Algebra Nat
  UniqueFactorizationMonoid

private lemma alpha_sq : (2 * θ - 1 : R) ^ 2 = -7 := by
  have h_theta_sq : θ ^ 2 = θ - 2 := theta_sq
  calc (2 * θ - 1 : R) ^ 2 = 4 * θ ^ 2 - 4 * θ + 1 := by ring
    _ = 4 * (θ - 2) - 4 * θ + 1 := by rw [h_theta_sq]
    _ = -7 := by ring

private lemma two_R_ne_zero : (2 : R) ≠ 0 := by
  intro h0
  have := congrArg QuadraticAlgebra.re h0; simp at this

private lemma theta_pow_mul_theta'_pow (m : ℕ) : θ ^ m * θ' ^ m = (2 : R) ^ m := by
  rw [theta'_eq_one_sub_theta, ← mul_pow, two_factorisation_R]

private lemma two_pow_R_im_zero (m : ℕ) : ((2 : R) ^ m).im = 0 := by
  rw [show (2 : R) ^ m = (((2 ^ m : ℕ) : ℤ) : R) from by push_cast; ring]
  exact QuadraticAlgebra.im_intCast _

private lemma alpha_ne_zero : (2 * θ - 1 : R) ≠ 0 := by
  intro h0
  have hsq := alpha_sq
  rw [h0, zero_pow two_ne_zero] at hsq
  have : ((0 : ℤ) : R) = ((-7 : ℤ) : R) := by exact_mod_cast hsq
  have := congrArg QuadraticAlgebra.re this; simp at this

private lemma binom_two_theta (d : ℕ) :
    (2 * θ) ^ d = ∑ k ∈ Finset.range (d + 1), ((d.choose k : ℤ) : R) * (2 * θ - 1) ^ k := by
  have h := add_pow (2 * θ - 1 : R) 1 d
  simp only [one_pow, mul_one] at h
  rw [show (2 * θ - 1 : R) + 1 = 2 * θ from by ring] at h
  rw [h]; exact Finset.sum_congr rfl (fun k _ => by push_cast; ring)

private lemma binom_two_one_sub_theta (d : ℕ) :
    (2 * (1 - θ)) ^ d =
      ∑ k ∈ Finset.range (d + 1), ((d.choose k : ℤ) : R) * (-(2 * θ - 1)) ^ k := by
  have h := add_pow (-(2 * θ - 1) : R) 1 d
  simp only [one_pow, mul_one] at h
  rw [show (-(2 * θ - 1) : R) + 1 = 2 * (1 - θ) from by ring] at h
  rw [h]; exact Finset.sum_congr rfl (fun k _ => by push_cast; ring)

/-- B_d = Σ_{j=0}^{(d-1)/2} C(d, 2j+1) · (-7)^j. -/
noncomputable def binomialB (d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range ((d + 1) / 2), (d.choose (2 * j + 1)) * (-7) ^ j

/-- `(2θ)^d - (2(1-θ))^d = 2·(2θ-1)·B_d`, the odd-part extraction from the binomial
    expansions, with the `α² = -7` substitution. -/
private lemma diff_two_pow_eq_binomB (d : ℕ) :
    (2 * θ) ^ d - (2 * (1 - θ)) ^ d = 2 * (2 * θ - 1) * ((binomialB d : ℤ) : R) := by
  set α : R := 2 * θ - 1 with hα_def
  have hα_sq : α ^ 2 = -7 := alpha_sq
  have hbinom_plus := binom_two_theta d
  have hbinom_minus := binom_two_one_sub_theta d
  rw [← hα_def] at hbinom_plus hbinom_minus
  rw [hbinom_plus, hbinom_minus, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (d + 1)) (p := Odd)]
  have h_even_zero : ∑ k ∈ Finset.filter (fun x => ¬Odd x) (Finset.range (d + 1)),
      (((d.choose k : ℤ) : R) * α ^ k - ((d.choose k : ℤ) : R) * (-α) ^ k) = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    simp only [Finset.mem_filter] at hk
    have h_ev : Even k := (Nat.even_or_odd k).resolve_right hk.2
    simp [Even.neg_pow h_ev, sub_self]
  rw [h_even_zero, add_zero]
  unfold binomialB
  push_cast
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun j _ => 2 * j + 1) ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_range] at hj ⊢
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨j, by ring⟩⟩
  · intro a b _ _ h_ab; linarith
  · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨j, hj⟩ := hk.2
    exact ⟨j, Finset.mem_range.mpr (by omega), hj.symm⟩
  · intro j hj
    simp only [Odd.neg_pow ⟨j, rfl⟩]
    have hpow : α ^ (2 * j + 1) = α * (α ^ 2) ^ j := by ring_nf
    rw [hpow, hα_sq]; ring

/-- The conjugate factors `(x ± √-7)/2` lie in `R` (since `x` is odd) and
    their product equals `(x²+7)/4 = 2^m = θ^m · θ'^m`. -/
lemma factors_in_R_with_product (x : ℤ) (m : ℕ) (hm_ge : m ≥ 3)
    (h : (x ^ 2 + 7) / 4 = 2 ^ m) :
    ∃ α β : R, α * β = θ ^ m * θ' ^ m ∧ α - β = 2 * θ - 1 := by
  -- Step 1: x must be odd
  have hx_odd : Odd x := by
    by_contra hx_not_odd
    rw [Int.not_odd_iff_even] at hx_not_odd
    obtain ⟨t, ht⟩ := hx_not_odd
    have hx2t : x = 2 * t := by omega
    have h_div : (x ^ 2 + 7) / 4 = t ^ 2 + 1 := by
      rw [hx2t]
      have : (2 * t) ^ 2 + 7 = (t ^ 2 + 1) * 4 + 3 := by ring
      omega
    rw [h_div] at h
    have h4_dvd_2m : (4 : ℤ) ∣ 2 ^ m :=
      ⟨2 ^ (m - 2), by
        rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_add]; congr 1; omega⟩
    have h4_dvd : (4 : ℤ) ∣ (t ^ 2 + 1) := h ▸ h4_dvd_2m
    rcases Int.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · have : (4 : ℤ) ∣ t ^ 2 := ⟨s ^ 2, by rw [hs]; ring⟩
      have : (4 : ℤ) ∣ 1 := (Int.dvd_add_right this).mp h4_dvd
      omega
    · have : (4 : ℤ) ∣ (t ^ 2 - 1) := ⟨s ^ 2 + s, by rw [hs]; ring⟩
      have h4_dvd_2 : (4 : ℤ) ∣ ((t ^ 2 + 1) - (t ^ 2 - 1)) := Int.dvd_sub h4_dvd this
      omega
  obtain ⟨k, hk⟩ := hx_odd
  -- (x²+7)/4 = k²+k+2 (exact division since x is odd)
  have hdiv : (x ^ 2 + 7) / 4 = k ^ 2 + k + 2 := by
    apply Int.ediv_eq_of_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
    rw [hk]; ring
  rw [hdiv] at h -- h : k^2 + k + 2 = 2^m
  -- α = k + θ, β = k + θ' = k + (1 - θ)
  refine ⟨(k : R) + θ, (k : R) + (1 - θ), ?_, ?_⟩
  · -- (k+θ)(k+(1-θ)) = k²+k+θ(1-θ) = k²+k+2 = 2^m = θ^m·θ'^m
    have h_two_R : (k : R) ^ 2 + (k : R) + 2 = (2 : R) ^ m := by
      have := congr_arg (fun n : ℤ => (n : R)) h
      push_cast at this; exact this
    rw [theta_pow_mul_theta'_pow, ← h_two_R]
    linear_combination two_factorisation_R
  · -- (k + θ) - (k + (1-θ)) = 2θ - 1
    ring

/-- The conjugate factors are coprime in R. -/
lemma conjugate_factors_coprime (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_diff : α - β = 2 * θ - 1) :
    IsCoprime α β := by
  apply isCoprime_of_prime_dvd
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    -- 0 - 0 = 2θ - 1, but 2θ - 1 ≠ 0
    simp only [sub_self] at h_diff
    -- (2θ - 1)² = -7 ≠ 0
    have h0 : (0 : R) = -7 := by
      have h' : (0 : R) ^ 2 = (2 * θ - 1) ^ 2 := by rw [h_diff]
      rw [alpha_sq] at h'
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h'
      exact h'
    have : ((0 : ℤ) : R) = ((-7 : ℤ) : R) := by exact_mod_cast h0
    have := congrArg QuadraticAlgebra.re this; simp at this
  · intro p hp hpa hpb
    -- 2 = θ * θ'; use p prime ⇒ p ∣ θ or p ∣ θ'
    have h_prod_val : α * β = (2 : R) ^ m := by
      rw [h_prod, ← mul_pow, theta_mul_theta']
    have h_p_dvd_two : p ∣ 2 := by
      have hp_dvd_pow : p ∣ (2 : R) ^ m := h_prod_val ▸ dvd_mul_of_dvd_left hpa β
      exact Prime.dvd_of_dvd_pow hp hp_dvd_pow
    -- p | (α - β) = 2θ - 1
    have h_p_dvd_diff : p ∣ (2 * θ - 1) := by rw [← h_diff]; exact dvd_sub hpa hpb
    -- N(2) = 4, N(2θ - 1) = 7; |N(p)| ∣ gcd(4, 7) = 1 ⇒ p is unit, contradiction
    have h_norm_two : QuadraticAlgebra.norm (2 : R) = 4 := by
      rw [show (2 : R) = ((2 : ℤ) : R) from by push_cast; rfl, QuadraticAlgebra.norm_intCast]
      norm_num
    have h_norm_diff : QuadraticAlgebra.norm (2 * θ - 1 : R) = 7 := by
      have : 2 * θ - 1 = (⟨-1, 2⟩ : R) := by
        apply QuadraticAlgebra.ext <;> simp [θ]
      rw [this, norm_eq]; ring
    have h_dvd_four : QuadraticAlgebra.norm p ∣ 4 := by
      rw [← h_norm_two]; exact map_dvd _ h_p_dvd_two
    have h_dvd_seven : QuadraticAlgebra.norm p ∣ 7 := by
      rw [← h_norm_diff]; exact map_dvd _ h_p_dvd_diff
    have h_np_dvd_one : QuadraticAlgebra.norm p ∣ 1 := by
      have h_dvd_gcd : (QuadraticAlgebra.norm p).natAbs ∣ Nat.gcd 4 7 :=
        Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr h_dvd_four)
          (Int.natAbs_dvd_natAbs.mpr h_dvd_seven)
      rw [show Nat.gcd 4 7 = 1 from by decide] at h_dvd_gcd
      rw [← Int.natAbs_dvd]
      exact_mod_cast h_dvd_gcd
    exact hp.not_unit (QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (isUnit_of_dvd_one h_np_dvd_one))

/-- If `α = ±1`, then `α - β` has im-component 0, but `2θ - 1` has im 2. -/
lemma factor_not_unit_left (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_diff : α - β = 2 * θ - 1) :
    ¬IsUnit α := by
  by_contra h_unit
  have h_cases : α = 1 ∨ α = -1 := by
    have := units_pm_one h_unit.unit; simpa [Units.ext_iff] using this
  rw [theta_pow_mul_theta'_pow] at h_prod
  have h2m_im := two_pow_R_im_zero m
  rcases h_cases with rfl | rfl
  · have hβ : β = (2 : R) ^ m := by simpa using h_prod
    rw [hβ] at h_diff
    have h_im := congrArg QuadraticAlgebra.im h_diff
    simp [θ, h2m_im] at h_im
  · have hβ : β = -((2 : R) ^ m) := by
      have hα : (-1 : R) * β = (2 : R) ^ m := h_prod
      linear_combination -hα
    rw [hβ] at h_diff
    have h_im := congrArg QuadraticAlgebra.im h_diff
    simp [θ, h2m_im] at h_im

lemma factor_not_unit_right (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_diff : α - β = 2 * θ - 1) :
    ¬IsUnit β := by
  by_contra h_unit
  have h_cases : β = 1 ∨ β = -1 := by
    have := units_pm_one h_unit.unit; simpa [Units.ext_iff] using this
  rw [theta_pow_mul_theta'_pow] at h_prod
  have h2m_im := two_pow_R_im_zero m
  rcases h_cases with rfl | rfl
  · have hα : α = (2 : R) ^ m := by simpa using h_prod
    rw [hα] at h_diff
    have h_im := congrArg QuadraticAlgebra.im h_diff
    simp [θ, h2m_im] at h_im
  · have hα : α = -((2 : R) ^ m) := by
      have h1 : α * (-1 : R) = (2 : R) ^ m := h_prod
      have h2 : -α = (2 : R) ^ m := by linear_combination h1
      linear_combination -h2
    rw [hα] at h_diff
    have h_im := congrArg QuadraticAlgebra.im h_diff
    simp [θ, h2m_im] at h_im

/-- From the dichotomy `α ∈ {±θ^m, ±θ'^m}` and the product relation, determine `β`,
    then take the difference α - β = 2θ-1 to obtain the conclusion. -/
lemma eliminate_x_conclude (α β : R) (m : ℕ)
    (h_diff : α - β = 2 * θ - 1)
    (h_assoc : (α = θ ^ m ∨ α = -(θ ^ m)) ∨ (α = θ' ^ m ∨ α = -(θ' ^ m)))
    (h_prod : α * β = θ ^ m * θ' ^ m) :
    (2 * θ - 1 = θ ^ m - θ' ^ m) ∨ (-2 * θ + 1 = θ ^ m - θ' ^ m) := by
  have hθ_ne : θ ≠ 0 := Irreducible.ne_zero theta_irreducible
  have hθ'_ne : θ' ≠ 0 := Irreducible.ne_zero theta'_irreducible
  rcases h_assoc with (rfl | rfl) | (rfl | rfl)
  · left
    have hβ : β = θ' ^ m := mul_left_cancel₀ (pow_ne_zero m hθ_ne) h_prod
    subst hβ
    linear_combination -h_diff
  · right
    have hβ : β = -(θ' ^ m) :=
      mul_left_cancel₀ (neg_ne_zero.mpr (pow_ne_zero m hθ_ne))
        (h_prod.trans (neg_mul_neg _ _).symm)
    subst hβ
    linear_combination h_diff
  · right
    have hβ : β = θ ^ m :=
      mul_left_cancel₀ (pow_ne_zero m hθ'_ne) (h_prod.trans (mul_comm _ _))
    subst hβ
    linear_combination h_diff
  · left
    have hβ : β = -(θ ^ m) :=
      mul_left_cancel₀ (neg_ne_zero.mpr (pow_ne_zero m hθ'_ne))
        (h_prod.trans ((mul_comm _ _).trans (neg_mul_neg _ _).symm))
    subst hβ
    linear_combination -h_diff

/-- The minus sign must hold in the disjunction. Proved by reducing modulo θ'²: if
    `2θ - 1 = θ^m - θ'^m`, then `θ^m - θ ≡ θ'^m - θ' (mod θ'²)`, and combining with
    `θ^m ≡ θ (mod θ'²)` (for odd m) and `θ'^m ≡ 0 (mod θ'²)` (m ≥ 2) forces
    θ'² ∣ θ',
    hence θ' is a unit — contradicting `units_pm_one`. -/
lemma must_have_minus_sign (m : ℕ) (hm_odd : Odd m) (hm_ge : m ≥ 3)
    (h : (2 * θ - 1 = θ ^ m - θ' ^ m) ∨ (-2 * θ + 1 = θ ^ m - θ' ^ m)) :
    (-2 * θ + 1 = θ ^ m - θ' ^ m) := by
  rcases h with h_plus | h_minus
  · exfalso
    have hθ' : θ' = 1 - θ := theta'_eq_one_sub_theta
    have hB : θ - θ' = 2 * θ - 1 := by rw [hθ']; ring
    have hC : θ ^ m - θ' ^ m = θ - θ' := h_plus.symm.trans hB.symm
    have step3 : θ' ^ 2 ∣ (θ ^ 2 - 1) := by
      have h_eq : θ ^ 2 - 1 = θ' * (θ' - 2) := by rw [hθ']; ring
      rw [h_eq, sq]
      apply mul_dvd_mul_left
      have h_dvd_2 : θ' ∣ (2 : R) := by
        refine ⟨θ, ?_⟩
        rw [mul_comm]; exact theta_mul_theta'.symm
      exact dvd_sub dvd_rfl h_dvd_2
    have step4 : θ' ^ 2 ∣ (θ ^ m - θ) := by
      obtain ⟨k, hk⟩ := hm_odd
      have h_eq : θ ^ m - θ = θ * ((θ ^ 2) ^ k - 1) := by
        rw [hk, show 2 * k + 1 = 1 + 2 * k from by ring,
            pow_add, pow_one, pow_mul, mul_sub, mul_one]
      rw [h_eq]
      exact dvd_mul_of_dvd_right
        (dvd_trans step3 (sub_one_dvd_pow_sub_one (θ ^ 2) k)) θ
    have step5 : θ' ^ 2 ∣ θ' := by
      have h_eq : θ ^ m - θ = θ' ^ m - θ' := by linear_combination hC
      have h_dvd_diff : θ' ^ 2 ∣ (θ' ^ m - θ') := by rwa [← h_eq]
      have h_dvd_pow : θ' ^ 2 ∣ θ' ^ m := pow_dvd_pow θ' (by omega : 2 ≤ m)
      have h := dvd_sub h_dvd_pow h_dvd_diff
      rwa [show θ' ^ m - (θ' ^ m - θ') = θ' from by ring] at h
    have hθ'_ne : θ' ≠ 0 := Irreducible.ne_zero theta'_irreducible
    have h_dvd_one : θ' ∣ 1 := by
      rw [sq] at step5
      have : θ' * θ' ∣ θ' * 1 := by rwa [mul_one]
      exact (mul_dvd_mul_iff_left hθ'_ne).mp this
    have h_unit := isUnit_of_dvd_one h_dvd_one
    obtain ⟨u, hu⟩ := h_unit
    rcases units_pm_one u with rfl | rfl <;>
      · have h_re_im := congrArg QuadraticAlgebra.im hu
        simp [θ'] at h_re_im
  · exact h_minus


theorem main_m_condition :
  ∀ x : ℤ, ∀ m : ℕ, Odd m → m ≥ 3 → (x ^ 2 + 7) / 4 = 2 ^ m →
    (-2*θ + 1 = θ^m - θ'^m) := by
  intro x m hm_odd hm_ge h_eq
  obtain ⟨α, β, h_prod, h_diff⟩ := factors_in_R_with_product x m hm_ge h_eq
  have h_coprime := conjugate_factors_coprime α β m h_prod h_diff
  have hα_not_unit : ¬IsUnit α := factor_not_unit_left α β m h_prod h_diff
  have hβ_not_unit : ¬IsUnit β := factor_not_unit_right α β m h_prod h_diff
  have h_assoc := ufd_power_association α β m h_prod h_coprime hα_not_unit hβ_not_unit
  have h_disj := eliminate_x_conclude α β m h_diff h_assoc h_prod
  exact must_have_minus_sign m hm_odd hm_ge h_disj

lemma reduction_divide_by_4 :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    (x ^ 2 + 7) / 4 = 2 ^ (n - 2) := by
  intro x n _ hn hx
  rw [hx]
  exact Int.ediv_eq_of_eq_mul_left (by norm_num)
    (by rw [show n = n - 2 + 2 from by omega, pow_add]; norm_num)


/-- From `-2θ + 1 = θ^m - θ'^m`, expand via the binomial theorem and reduce
    modulo 7 to obtain `-2^(m-1) ≡ m (mod 7)`. -/
lemma expand_by_binomial (m : ℕ) (hm_ge : m ≥ 3)
    (h : -2 * θ + 1 = θ ^ m - θ' ^ m) :
    -(2 : ℤ) ^ (m - 1) % 7 = (m : ℤ) % 7 := by
  -- Working in R now (no K detour). Let α := 2θ - 1; then α² = -7.
  set α : R := 2 * θ - 1 with hα_def
  have hα_sq : α ^ 2 = -7 := alpha_sq
  have hθ' : θ' = 1 - θ := theta'_eq_one_sub_theta
  have hne : α ≠ 0 := alpha_ne_zero
  -- step1 : -2^m·α = (2θ)^m - (2(1-θ))^m
  have step1 : -(2 : R) ^ m * α = (2 * θ) ^ m - (2 * (1 - θ)) ^ m := by
    have hexp : θ ^ m - θ' ^ m = -α := by
      rw [hα_def]; linear_combination -h
    rw [mul_pow, mul_pow, ← hθ']
    linear_combination -(2 : R) ^ m * hexp
  -- ∃ q : ℤ, -2^(m-1) = m + 7*q
  have step2 : ∃ q : ℤ, -(2 : ℤ) ^ (m - 1) = ↑m + 7 * q := by
    -- (2θ)^m - (2(1-θ))^m = 2·α·S where S = Σ_{j} C(m, 2j+1)·(-7)^j
    have hdiff : ∃ S : ℤ, (2 * θ) ^ m - (2 * (1 - θ)) ^ m =
        (2 : R) * α * (S : R) := by
      refine ⟨-(2 : ℤ) ^ (m - 1), ?_⟩
      rw [← step1]
      push_cast
      have h2m : (2 : R) ^ m = 2 ^ (m - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m by omega)]
        rw [pow_succ]
      rw [h2m]
      ring
    obtain ⟨S, hS⟩ := hdiff
    have hcancel : -(2 : ℤ) ^ (m - 1) = S := by
      have h1 : -(2 : R) ^ m = 2 * (S : R) :=
        mul_right_cancel₀ hne (by linear_combination step1.trans hS)
      have h2 : ((-(2 : ℤ) ^ m : ℤ) : R) = ((2 * S : ℤ) : R) := by
        push_cast; exact h1
      have h3 : -(2 : ℤ) ^ m = 2 * S := Int.cast_injective h2
      have h6 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m by omega)]
        rw [pow_succ]; ring
      linarith
    -- Now show S ≡ m (mod 7); S = binomialB m, which is ≡ m (mod 7)
    have hT_mod : ∃ q : ℤ, binomialB m = ↑m + 7 * q := by
      rw [binomialB, show (m + 1) / 2 = ((m + 1) / 2 - 1) + 1 from by omega,
        Finset.sum_range_succ']
      have hfirst : (m.choose (2 * 0 + 1) : ℤ) * (-7 : ℤ) ^ 0 = (m : ℤ) := by
        simp [Nat.choose_one_right]
      rw [hfirst]
      refine ⟨∑ j ∈ Finset.range ((m + 1) / 2 - 1),
        (m.choose (2 * (j + 1) + 1) : ℤ) * (-1) * (-7 : ℤ) ^ j, ?_⟩
      have key : ∑ j ∈ Finset.range ((m + 1) / 2 - 1),
        (m.choose (2 * (j + 1) + 1) : ℤ) * (-7 : ℤ) ^ (j + 1) =
        7 * ∑ j ∈ Finset.range ((m + 1) / 2 - 1),
          (m.choose (2 * (j + 1) + 1) : ℤ) * (-1) * (-7 : ℤ) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      linarith
    -- S = binomialB m via the shared R identity and ℤ → R injectivity
    have hS_eq : S = binomialB m := by
      have h2α_ne : (2 : R) * α ≠ 0 := mul_ne_zero two_R_ne_zero hne
      apply Int.cast_injective (α := R)
      apply mul_left_cancel₀ h2α_ne
      rw [← hS, hα_def, diff_two_pow_eq_binomB m]
    obtain ⟨q, hq⟩ := hT_mod
    exact ⟨q, by rw [hcancel, hS_eq, hq]⟩
  obtain ⟨q, hq⟩ := step2
  rw [hq]
  omega


/-- Key consequence of unique factorization in ℤ[(1+√-7)/2]:
    For odd n ≥ 5, if x² + 7 = 2ⁿ, then setting m = n - 2, we have
    -2^(m-1) ≡ m (mod 7). -/
lemma odd_case_mod_seven_constraint :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    -(2 : ℤ) ^ (n - 3) % 7 = ((n : ℤ) - 2) % 7 := by
      intro x n hn_odd hn_ge h_eq
      have h_div := reduction_divide_by_4 x n hn_odd hn_ge h_eq
      have hm_odd : Odd (n - 2) := by
        obtain ⟨k, hk⟩ := hn_odd; exact ⟨k - 1, by omega⟩
      have hm_ge : n - 2 ≥ 3 := by omega
      have h_theta := main_m_condition x (n - 2) hm_odd hm_ge h_div
      have h_mod := expand_by_binomial (n - 2) hm_ge h_theta
      rwa [show n - 3 = (n - 2) - 1 from by omega,
        show ((n : ℤ) - 2) = ((n - 2 : ℕ) : ℤ) from by omega]

private lemma two_pow_six_pow_emod_seven (q : ℕ) : ((2 : ℤ) ^ 6) ^ q % 7 = 1 := by
  induction q with
  | zero => norm_num
  | succ q ih => rw [pow_succ, Int.mul_emod, ih]; norm_num

/-- From -2^(m-1) ≡ m (mod 7) and 2⁶ ≡ 1 (mod 7), the only solutions are
    m ≡ 3, 5, or 13 (mod 42). -/
theorem odd_case_only_three_values_mod_42 :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    (n - 2) % 42 = 3 ∨ (n - 2) % 42 = 5 ∨ (n - 2) % 42 = 13 := by
      intro x n hn_odd hn_ge h_eq
      have h_mod7 := odd_case_mod_seven_constraint x n hn_odd hn_ge h_eq
      set m := n - 2 with hm_def
      have hm_ge : m ≥ 3 := by omega
      have hm_odd : Odd m := by
        obtain ⟨k, hk⟩ := hn_odd; exact ⟨k - 1, by omega⟩
      have hn3_eq : n - 3 = m - 1 := by omega
      rw [hn3_eq] at h_mod7
      have hcast : (↑n : ℤ) - 2 = ↑m := by omega
      rw [hcast] at h_mod7
      have hm_mod6 : m % 6 = 1 ∨ m % 6 = 3 ∨ m % 6 = 5 := by
        obtain ⟨k, hk⟩ := hm_odd; omega
      rcases hm_mod6 with h6 | h6 | h6
      · right; right
        have h_pow_mod : (2 : ℤ) ^ (m - 1) % 7 = 1 := by
          obtain ⟨q, hq⟩ : 6 ∣ (m - 1) := ⟨(m - 1) / 6, by omega⟩
          rw [show (m : ℕ) - 1 = 6 * q from by omega, pow_mul]
          exact two_pow_six_pow_emod_seven q
        omega
      · left
        have h_pow_mod : (2 : ℤ) ^ (m - 1) % 7 = 4 := by
          obtain ⟨q, hq⟩ : ∃ q, m - 1 = 6 * q + 2 := ⟨(m - 1) / 6, by omega⟩
          rw [hq, pow_add, pow_mul, Int.mul_emod, two_pow_six_pow_emod_seven q]; norm_num
        omega
      · right; left
        have h_pow_mod : (2 : ℤ) ^ (m - 1) % 7 = 2 := by
          obtain ⟨q, hq⟩ : ∃ q, m - 1 = 6 * q + 4 := ⟨(m - 1) / 6, by omega⟩
          rw [hq, pow_add, pow_mul, Int.mul_emod, two_pow_six_pow_emod_seven q]; norm_num
        omega

/-! ## Skeleton for the uniqueness argument -/

lemma corollary_C (x₁ x₂ : ℤ) (m₁ m₂ : ℕ)
    (h₁_odd : Odd m₁) (h₂_odd : Odd m₂)
    (h₁_ge : m₁ ≥ 3) (h₂_ge : m₂ ≥ 3)
    (h₁_eq : (x₁ ^ 2 + 7) / 4 = 2 ^ m₁)
    (h₂_eq : (x₂ ^ 2 + 7) / 4 = 2 ^ m₂) :
    θ ^ m₁ - θ' ^ m₁ = θ ^ m₂ - θ' ^ m₂ := by
  have h1 := main_m_condition x₁ m₁ h₁_odd h₁_ge h₁_eq
  have h2 := main_m_condition x₂ m₂ h₂_odd h₂_ge h₂_eq
  rw [← h1, ← h2]

private lemma seven_pow_gt_two_mul_add_one (j : ℕ) (hj : j ≥ 1) :
    7 ^ j > 2 * j + 1 := by
  induction j with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => norm_num
    | succ m =>
      have : 7 ^ (m + 2) = 7 * 7 ^ (m + 1) := by ring
      omega

private lemma j_gt_padicValNat_two_mul_add_one (j : ℕ) (hj : j ≥ 1) :
    j > padicValNat 7 (2 * j + 1) := by
  set m := padicValNat 7 (2 * j + 1)
  by_contra h_le
  push Not at h_le
  have h_dvd : 7 ^ m ∣ (2 * j + 1) := pow_padicValNat_dvd
  have h_le2 : 7 ^ m ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) h_dvd
  have h_le3 : 7 ^ j ≤ 7 ^ m := Nat.pow_le_pow_right (by norm_num) h_le
  exact absurd (Nat.lt_of_lt_of_le (seven_pow_gt_two_mul_add_one j hj) (le_refl _))
    (not_lt.mpr (le_trans h_le3 h_le2))

private lemma higher_term_nat_dvd (d l j : ℕ) (hd : d > 0) (hj : j ≥ 1)
    (h_div : 7 ^ l ∣ d) (hk : 2 * j + 1 ≤ d) :
    7 ^ (l + 1) ∣ d.choose (2 * j + 1) * 7 ^ j := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  set C := d.choose (2 * j + 1) with hC_def
  set k := 2 * j + 1 with hk_def
  have hC_pos : C > 0 := Nat.choose_pos hk
  have hC_ne : C ≠ 0 := by omega
  have hk_ne : k ≠ 0 := by omega
  have h_absorb : d * (d - 1).choose (2 * j) = C * k := by
    have hds : d - 1 + 1 = d := by omega
    have h := Nat.add_one_mul_choose_eq (d - 1) (2 * j)
    rw [hds] at h; exact h
  have h_dvd_prod : 7 ^ l ∣ C * k := by
    rw [← h_absorb]; exact dvd_trans h_div (dvd_mul_right d _)
  have h_val_prod : l ≤ padicValNat 7 (C * k) :=
    (padicValNat_dvd_iff_le (mul_ne_zero hC_ne hk_ne)).mp h_dvd_prod
  have h_val_mul : padicValNat 7 (C * k) = padicValNat 7 C + padicValNat 7 k :=
    padicValNat.mul hC_ne hk_ne
  have h_j_gt : j > padicValNat 7 k := by
    rw [hk_def]; exact j_gt_padicValNat_two_mul_add_one j hj
  have h_val_pow : padicValNat 7 (C * 7 ^ j) = padicValNat 7 C + j := by
    rw [padicValNat.mul hC_ne (by positivity), padicValNat.prime_pow]
  exact (padicValNat_dvd_iff_le (mul_ne_zero hC_ne (by positivity))).mpr (by omega)

lemma lemma_A_binomial_valuation (d l : ℕ) (hd : d > 0)
    (h_div : (7 : ℤ) ^ l ∣ ↑d) (h_ndiv : ¬ (7 : ℤ) ^ (l + 1) ∣ ↑d) :
    (7 : ℤ) ^ l ∣ binomialB d ∧ ¬ (7 : ℤ) ^ (l + 1) ∣ binomialB d := by
  set n := (d + 1) / 2 with hn_def
  set f : ℕ → ℤ := fun j => ↑(d.choose (2 * j + 1)) * (-7) ^ j with hf_def
  have hn_pos : n ≥ 1 := by omega
  have h_f0 : f 0 = ↑d := by simp [hf_def, Nat.choose_one_right]
  have h_split : binomialB d = f 0 + ∑ j ∈ Finset.range (n - 1), f (j + 1) := by
    unfold binomialB
    conv_lhs => rw [show (d + 1) / 2 = (n - 1) + 1 from by omega]
    rw [Finset.sum_range_succ']
    ring
  have h_div_nat : 7 ^ l ∣ d := by exact_mod_cast h_div
  have h_higher : ∀ j ∈ Finset.range (n - 1), (7 : ℤ) ^ (l + 1) ∣ f (j + 1) := by
    intro j hj
    simp only [hf_def]
    have hj_mem := Finset.mem_range.mp hj
    have hk_le : 2 * (j + 1) + 1 ≤ d := by omega
    have h_nat := higher_term_nat_dvd d l (j + 1) hd (by omega) h_div_nat hk_le
    have h_int : (7 : ℤ) ^ (l + 1) ∣ ↑(d.choose (2 * (j + 1) + 1)) * (7 : ℤ) ^ (j + 1) := by
      exact_mod_cast h_nat
    have h_neg7 : (-7 : ℤ) ^ (j + 1) = (-1) ^ (j + 1) * (7 : ℤ) ^ (j + 1) := by
      rw [show (-7 : ℤ) = (-1) * 7 from by ring, mul_pow]
    rw [h_neg7, show (↑(d.choose (2 * (j + 1) + 1)) : ℤ) *
      ((-1 : ℤ) ^ (j + 1) * (7 : ℤ) ^ (j + 1)) =
      (-1) ^ (j + 1) * (↑(d.choose (2 * (j + 1) + 1)) * (7 : ℤ) ^ (j + 1)) from by ring]
    exact dvd_mul_of_dvd_right h_int _
  have h_tail : (7 : ℤ) ^ (l + 1) ∣ ∑ j ∈ Finset.range (n - 1), f (j + 1) :=
    Finset.dvd_sum h_higher
  constructor
  · rw [h_split, h_f0]
    exact dvd_add h_div (dvd_trans (pow_dvd_pow 7 (by omega : l ≤ l + 1)) h_tail)
  · intro h_contra
    apply h_ndiv
    rw [h_split, h_f0] at h_contra
    have := dvd_sub h_contra h_tail
    simpa using this

/-- A'_d = Σ_{j=0}^{d/2-1} C(d, 2(j+1)) · (-7)^j. -/
noncomputable def binomialA' (d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (d / 2), (d.choose (2 * (j + 1)) : ℤ) * (-7) ^ j

private lemma higher_even_term_nat_dvd (d l j : ℕ) (hd : d > 0) (hj : j ≥ 1)
    (h_div : 7 ^ l ∣ d) (hk : 2 * (j + 1) ≤ d) :
    7 ^ (l + 1) ∣ d.choose (2 * (j + 1)) * 7 ^ j := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  set C := d.choose (2 * (j + 1)) with hC_def
  set k := 2 * (j + 1) with hk_def
  have hC_pos : C > 0 := Nat.choose_pos hk
  have hC_ne : C ≠ 0 := by omega
  have hk_ne : k ≠ 0 := by omega
  have h_absorb : d * (d - 1).choose (2 * j + 1) = C * k := by
    have hds : d - 1 + 1 = d := by omega
    have h := Nat.add_one_mul_choose_eq (d - 1) (2 * j + 1)
    rw [hds] at h; exact h
  have h_dvd_prod : 7 ^ l ∣ C * k := by
    rw [← h_absorb]; exact dvd_trans h_div (dvd_mul_right d _)
  have h_val_prod : l ≤ padicValNat 7 (C * k) :=
    (padicValNat_dvd_iff_le (mul_ne_zero hC_ne hk_ne)).mp h_dvd_prod
  have h_val_mul : padicValNat 7 (C * k) = padicValNat 7 C + padicValNat 7 k :=
    padicValNat.mul hC_ne hk_ne
  have h_j_gt : j > padicValNat 7 k := by
    rw [hk_def]
    set m := padicValNat 7 (2 * (j + 1))
    by_contra h_le
    push Not at h_le
    have h_dvd : 7 ^ m ∣ (2 * (j + 1)) := pow_padicValNat_dvd
    have h_le2 : 7 ^ m ≤ 2 * (j + 1) := Nat.le_of_dvd (by omega) h_dvd
    have h_le3 : 7 ^ j ≤ 7 ^ m := Nat.pow_le_pow_right (by norm_num) h_le
    have h_gt : 7 ^ j > 2 * j + 1 := seven_pow_gt_two_mul_add_one j hj
    have h_eq : 7 ^ j = 2 * (j + 1) := by omega
    exact absurd (h_eq ▸ even_two_mul (j + 1)) (Nat.not_even_iff_odd.mpr (Odd.pow (by decide)))
  have h_val_pow : padicValNat 7 (C * 7 ^ j) = padicValNat 7 C + j := by
    rw [padicValNat.mul hC_ne (by positivity), padicValNat.prime_pow]
  exact (padicValNat_dvd_iff_le (mul_ne_zero hC_ne (by positivity))).mpr (by omega)

lemma even_binomial_valuation (d l : ℕ) (hd : d > 0)
    (h_div : (7 : ℤ) ^ l ∣ ↑d) (h_ndiv : ¬ (7 : ℤ) ^ (l + 1) ∣ ↑d)
    (h_7_dvd : 7 ∣ d) :
    (7 : ℤ) ^ l ∣ binomialA' d ∧ ¬ (7 : ℤ) ^ (l + 1) ∣ binomialA' d := by
  set n := d / 2 with hn_def
  set f : ℕ → ℤ := fun j => ↑(d.choose (2 * (j + 1))) * (-7) ^ j with hf_def
  have hn_pos : n ≥ 1 := by omega
  have h_even : 2 ∣ d * (d - 1) := by
    by_cases h : 2 ∣ d
    · exact h.mul_right (d - 1)
    · have h2 : 2 ∣ d - 1 := by omega
      exact h2.mul_left d
  have h_f0 : f 0 = ↑(d.choose 2) := by simp [hf_def]
  have h_choose2 : d.choose 2 = d * (d - 1) / 2 := Nat.choose_two_right d
  have h_f0_div : (7 : ℤ) ^ l ∣ f 0 := by
    rw [h_f0, h_choose2]
    have h_div_nat : 7 ^ l ∣ d := by exact_mod_cast h_div
    have h_div_prod_nat : 7 ^ l ∣ d * (d - 1) := dvd_mul_of_dvd_left h_div_nat (d - 1)
    have : 7 ^ l ∣ d * (d - 1) / 2 := by
      rw [Nat.dvd_div_iff_mul_dvd h_even]
      exact (Nat.Coprime.pow_right _ (by decide : Nat.Coprime 2 7)).mul_dvd_of_dvd_of_dvd
        h_even h_div_prod_nat
    exact_mod_cast this
  have h_f0_ndiv : ¬ (7 : ℤ) ^ (l + 1) ∣ f 0 := by
    rw [h_f0]
    intro h_contra
    apply h_ndiv
    have h_choose_nat : 7 ^ (l + 1) ∣ d.choose 2 := by exact_mod_cast h_contra
    rw [h_choose2] at h_choose_nat
    have h_dvd_prod : 7 ^ (l + 1) ∣ d * (d - 1) := by
      rw [← Nat.div_mul_cancel h_even]
      exact h_choose_nat.mul_right 2
    have h_cop_d1 : Nat.Coprime (7 ^ (l + 1)) (d - 1) := by
      apply Nat.Coprime.pow_left
      exact (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (by omega)
    exact_mod_cast h_cop_d1.dvd_of_dvd_mul_right h_dvd_prod
  have h_split : binomialA' d = f 0 + ∑ j ∈ Finset.range (n - 1), f (j + 1) := by
    unfold binomialA'
    conv_lhs => rw [show d / 2 = (n - 1) + 1 from by omega]
    rw [Finset.sum_range_succ']
    ring
  have h_div_nat : 7 ^ l ∣ d := by exact_mod_cast h_div
  have h_higher : ∀ j ∈ Finset.range (n - 1), (7 : ℤ) ^ (l + 1) ∣ f (j + 1) := by
    intro j hj
    simp only [hf_def]
    have hj_mem := Finset.mem_range.mp hj
    have hk_le : 2 * ((j + 1) + 1) ≤ d := by omega
    have h_nat := higher_even_term_nat_dvd d l (j + 1) hd (by omega) h_div_nat hk_le
    have h_int :
        (7 : ℤ) ^ (l + 1) ∣ ↑(d.choose (2 * ((j + 1) + 1))) * (7 : ℤ) ^ (j + 1) := by
      exact_mod_cast h_nat
    have h_neg7 : (-7 : ℤ) ^ (j + 1) = (-1) ^ (j + 1) * (7 : ℤ) ^ (j + 1) := by
      rw [show (-7 : ℤ) = (-1) * 7 from by ring, mul_pow]
    rw [h_neg7, show (↑(d.choose (2 * ((j + 1) + 1))) : ℤ) *
      ((-1 : ℤ) ^ (j + 1) * (7 : ℤ) ^ (j + 1)) =
      (-1) ^ (j + 1) * (↑(d.choose (2 * ((j + 1) + 1))) * (7 : ℤ) ^ (j + 1)) from by ring]
    exact dvd_mul_of_dvd_right h_int _
  have h_tail : (7 : ℤ) ^ (l + 1) ∣ ∑ j ∈ Finset.range (n - 1), f (j + 1) :=
    Finset.dvd_sum h_higher
  constructor
  · rw [h_split]
    exact dvd_add h_f0_div (dvd_trans (pow_dvd_pow 7 (by omega : l ≤ l + 1)) h_tail)
  · intro h_contra
    apply h_f0_ndiv
    rw [h_split] at h_contra
    have := dvd_sub h_contra h_tail
    simpa using this

/-- a(n) = θ^n + θ'^n, an integer recurrence. -/
def traceSeq : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => traceSeq (n + 1) - 2 * traceSeq n

lemma traceSeq_eq (n : ℕ) : (traceSeq n : R) = θ ^ n + θ' ^ n := by
  induction n using traceSeq.induct with
  | case1 =>
    simp only [traceSeq, Int.cast_ofNat, pow_zero]
    ring
  | case2 =>
    simp only [traceSeq, Int.cast_one, pow_one]
    have h_theta' : θ' = 1 - θ := theta'_eq_one_sub_theta
    rw [h_theta']; ring
  | case3 n ih1 ih2 =>
    simp only [traceSeq, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    rw [ih1, ih2]
    have h_prod : θ * θ' = 2 := theta_mul_theta'
    have h_sum : θ + θ' = 1 := theta_add_theta'
    have key : θ ^ (n + 2) + θ' ^ (n + 2) =
        (θ + θ') * (θ ^ (n + 1) + θ' ^ (n + 1)) - θ * θ' * (θ ^ n + θ' ^ n) := by ring
    rw [key, h_sum, h_prod]
    ring

private lemma traceSeq_mod7_period (m : ℕ) :
    traceSeq m % 7 = traceSeq (m % 3) % 7 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | m + 3 =>
      have h1 := ih (m + 2) (by omega)
      have h2 := ih (m + 1) (by omega)
      conv_lhs => rw [show traceSeq (m + 3) =
        traceSeq (m + 2) - 2 * traceSeq (m + 1) from rfl]
      have key : (traceSeq (m + 2) - 2 * traceSeq (m + 1)) % 7 =
          (traceSeq ((m + 2) % 3) - 2 * traceSeq ((m + 1) % 3)) % 7 := by omega
      rw [show (m + 3) % 3 = m % 3 from by omega, key]
      have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h0 | h1' | h2'
      · rw [h0, show (m + 2) % 3 = 2 from by omega,
             show (m + 1) % 3 = 1 from by omega]; simp [traceSeq]
      · rw [h1', show (m + 2) % 3 = 0 from by omega,
             show (m + 1) % 3 = 2 from by omega]; simp [traceSeq]
      · rw [h2', show (m + 2) % 3 = 1 from by omega,
             show (m + 1) % 3 = 0 from by omega]; simp [traceSeq]

lemma traceSeq_not_dvd_seven (n : ℕ) : ¬((7 : ℤ) ∣ traceSeq n) := by
  intro ⟨k, hk⟩
  have h := traceSeq_mod7_period n
  rw [hk] at h; simp only [Int.mul_emod_right] at h
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h0 | h1 | h2
  · rw [h0] at h; simp [traceSeq] at h
  · rw [h1] at h; simp [traceSeq] at h
  · rw [h2] at h; simp [traceSeq] at h

lemma nat_even_iff_not_odd (n : ℕ) : Even n ↔ ¬ Odd n := by
  exact Iff.symm not_odd_iff_even

/-- The key algebraic identity behind `at_most_one_m_per_class`, proved in `R` and
    lifted back to `ℤ` via injectivity of `ℤ → R`: if `P = θ ^ m + θ' ^ m`,
    `-2θ + 1 = θ ^ m - θ' ^ m`, and `θ ^ m - θ' ^ m = θ ^ (m + d) - θ' ^ (m + d)`,
    then `P · B_d = 1 - 7 · A'_d - 2 ^ d`. -/
private lemma trace_mul_binomialB_eq (P : ℤ) (m d : ℕ)
    (hP_eq : (P : R) = θ ^ m + θ' ^ m)
    (h_theta : -2 * θ + 1 = θ ^ m - θ' ^ m)
    (h_pow_eq : θ ^ m - θ' ^ m = θ ^ m * θ ^ d - θ' ^ m * θ' ^ d) :
    P * binomialB d = 1 - 7 * binomialA' d - (2 : ℤ) ^ d := by
  have h_theta' : θ' = 1 - θ := theta'_eq_one_sub_theta
  set α : R := 2 * θ - 1 with hα_def
  have hα_sq : α ^ 2 = -7 := alpha_sq
  have hα_ne : α ≠ 0 := alpha_ne_zero
  have h_cross : (θ ^ m + θ' ^ m) * (θ ^ d - θ' ^ d) =
      -(θ ^ m - θ' ^ m) * (θ ^ d + θ' ^ d - 2) := by
    linear_combination -2 * h_pow_eq
  have h_diff_eq : θ ^ m - θ' ^ m = -α := by
    rw [← h_theta, hα_def]; ring
  -- Binomial expansions in R
  have hbinom_plus := binom_two_theta d
  have hbinom_minus := binom_two_one_sub_theta d
  rw [← hα_def] at hbinom_plus hbinom_minus
  have h_diff_binom : (2 * θ) ^ d - (2 * (1 - θ)) ^ d =
      2 * α * ((binomialB d : ℤ) : R) := by rw [hα_def]; exact diff_two_pow_eq_binomB d
  have h_sum_binom : (2 * θ) ^ d + (2 * (1 - θ)) ^ d =
      2 * (1 - 7 * ((binomialA' d : ℤ) : R)) := by
    rw [hbinom_plus, hbinom_minus, ← Finset.sum_add_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (d+1)) (p := Odd)]
    have h_odd_zero : ∑ k ∈ Finset.filter Odd (Finset.range (d + 1)),
        (((d.choose k : ℤ) : R) * α ^ k + ((d.choose k : ℤ) : R) * (-α) ^ k) = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      simp only [Finset.mem_filter] at hk
      rw [Odd.neg_pow hk.2]; ring
    rw [h_odd_zero, zero_add]
    unfold binomialA'
    push_cast
    rw [show (2 : R) * (1 - 7 * ∑ j ∈ Finset.range (d / 2),
           (d.choose (2 * (j + 1)) : R) * (-7 : R) ^ j) =
         2 + ∑ j ∈ Finset.range (d / 2),
           2 * (d.choose (2 * (j + 1)) : R) * (-7 : R) ^ (j + 1) from by
      rw [mul_sub, mul_one]
      rw [← mul_assoc, Finset.mul_sum]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring]
    simp_rw [← nat_even_iff_not_odd]
    rw [show Finset.filter Even (Finset.range (d + 1)) =
           Finset.image (fun j => 2 * j) (Finset.range (d / 2 + 1)) from by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Even]
      constructor
      · rintro ⟨hk, m, rfl⟩
        refine ⟨m, ?_, (two_mul m)⟩
        omega
      · rintro ⟨m, hm, rfl⟩
        refine ⟨by omega, ⟨m, two_mul m⟩⟩]
    rw [Finset.sum_image (fun a _ b _ hab => by omega)]
    rw [show d / 2 + 1 = (d / 2) + 1 from rfl]
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, pow_zero, mul_one, Nat.cast_one, mul_zero]
    norm_num
    rw [add_comm _ (2 : R)]
    rw [add_left_cancel_iff]
    apply Finset.sum_congr rfl
    intro j _
    have : α ^ (2 * (j + 1)) = (α ^ 2) ^ (j + 1) := by ring_nf
    rw [this, hα_sq]; ring
  have h_in_R : 2 * (P : R) * ((binomialB d : ℤ) : R) =
      2 * ((1 : R) - 7 * ((binomialA' d : ℤ) : R) - (2 : R) ^ d) := by
    have h_sub1 : (P : R) * (θ ^ d - θ' ^ d) =
        α * (θ ^ d + θ' ^ d - 2) := by
      rw [hP_eq, h_cross, h_diff_eq]; ring
    have h_scaled : (P : R) * ((2 : R) ^ d * (θ ^ d - θ' ^ d)) =
        α * ((2 : R) ^ d * (θ ^ d + θ' ^ d) - (2 : R) ^ d * 2) := by
      calc (P : R) * ((2 : R) ^ d * (θ ^ d - θ' ^ d))
          = (2 : R) ^ d * ((P : R) * (θ ^ d - θ' ^ d)) := by ring
        _ = (2 : R) ^ d * (α * (θ ^ d + θ' ^ d - 2)) := by rw [h_sub1]
        _ = α * ((2 : R) ^ d * (θ ^ d + θ' ^ d) - (2 : R) ^ d * 2) := by ring
    have h_lhs_eq : (2 : R) ^ d * (θ ^ d - θ' ^ d) =
        (2 * θ) ^ d - (2 * (1 - θ)) ^ d := by
      rw [mul_pow, mul_pow, h_theta']; ring
    rw [h_lhs_eq, h_diff_binom] at h_scaled
    have h_rhs_eq : (2 : R) ^ d * (θ ^ d + θ' ^ d) =
        (2 * θ) ^ d + (2 * (1 - θ)) ^ d := by
      rw [mul_pow, mul_pow, h_theta']; ring
    rw [h_rhs_eq, h_sum_binom] at h_scaled
    have h_cancel : α * (2 * (P : R) * ((binomialB d : ℤ) : R)) =
        α * (2 * (1 - 7 * ((binomialA' d : ℤ) : R) - (2 : R) ^ d)) := by
      linear_combination h_scaled
    exact mul_left_cancel₀ hα_ne h_cancel
  apply Int.cast_injective (α := R)
  have h_lhs : ((P * binomialB d : ℤ) : R) = (P : R) * ((binomialB d : ℤ) : R) := by
    push_cast; ring
  have h_rhs : ((1 - 7 * binomialA' d - (2 : ℤ) ^ d : ℤ) : R) =
      (1 : R) - 7 * ((binomialA' d : ℤ) : R) - (2 : R) ^ d := by push_cast; ring
  rw [h_lhs, h_rhs]
  rw [mul_assoc] at h_in_R
  exact mul_left_cancel₀ two_R_ne_zero h_in_R

/-- Each residue class mod 42 has at most one m solving the equation. -/
lemma at_most_one_m_per_class (m₁ m₂ : ℕ)
    (h₁_odd : Odd m₁) (h₂_odd : Odd m₂)
    (h₁_ge : m₁ ≥ 3) (h₂_ge : m₂ ≥ 3)
    (h_cong : m₁ % 42 = m₂ % 42)
    (h₁_theta : -2 * θ + 1 = θ ^ m₁ - θ' ^ m₁)
    (h₂_theta : -2 * θ + 1 = θ ^ m₂ - θ' ^ m₂) :
    m₁ = m₂ := by
  by_contra h_ne
  wlog h_lt : m₁ < m₂ with H
  · exact H m₂ m₁ h₂_odd h₁_odd h₂_ge h₁_ge h_cong.symm h₂_theta h₁_theta
      (Ne.symm h_ne) (by omega)
  set d := m₂ - m₁ with hd_def
  have hd_pos : d > 0 := by omega
  have h_42_dvd : 42 ∣ d := by
    rw [hd_def]
    exact (Nat.modEq_iff_dvd' h_lt.le).mp h_cong
  have h_7_dvd : (7 : ℕ) ∣ d := Nat.dvd_trans (by norm_num : 7 ∣ 42) h_42_dvd
  set l := padicValNat 7 d with hl_def
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hl_pos : l ≥ 1 := one_le_padicValNat_of_dvd (by omega) h_7_dvd
  have h_div : (7 : ℤ) ^ l ∣ ↑d := by exact_mod_cast pow_padicValNat_dvd
  have h_ndiv : ¬ (7 : ℤ) ^ (l + 1) ∣ ↑d := by
    intro h_contra
    have h_nat : 7 ^ (l + 1) ∣ d := by exact_mod_cast h_contra
    have := (padicValNat_dvd_iff_le (by omega : d ≠ 0)).mp h_nat
    omega
  have h_eq : θ ^ m₁ - θ' ^ m₁ = θ ^ m₂ - θ' ^ m₂ :=
    h₁_theta.symm.trans h₂_theta
  have h_val := lemma_A_binomial_valuation d l hd_pos h_div h_ndiv
  have h_trace : ∃ P : ℤ, (P : R) = θ ^ m₁ + θ' ^ m₁ ∧ ¬((7 : ℤ) ∣ P) :=
    ⟨traceSeq m₁, traceSeq_eq m₁, traceSeq_not_dvd_seven m₁⟩
  obtain ⟨P, hP_eq, hP_coprime⟩ := h_trace
  have h_pow_eq : θ ^ m₁ - θ' ^ m₁ = θ ^ m₁ * θ ^ d - θ' ^ m₁ * θ' ^ d := by
    have h_m2_eq : m₂ = m₁ + d := by omega
    rw [h_m2_eq, pow_add, pow_add] at h_eq
    exact h_eq
  -- Key algebraic identity in R, lifted back to ℤ via `trace_mul_binomialB_eq`
  have h_identity : P * binomialB d = 1 - 7 * binomialA' d - (2 : ℤ) ^ d :=
    trace_mul_binomialB_eq P m₁ d hP_eq h₁_theta h_pow_eq
  have h_even_val : (7 : ℤ) ^ l ∣ binomialA' d ∧ ¬ (7 : ℤ) ^ (l + 1) ∣ binomialA' d :=
    even_binomial_valuation d l hd_pos h_div h_ndiv h_7_dvd
  have h_3_dvd : 3 ∣ d := Nat.dvd_trans (by norm_num : 3 ∣ 42) h_42_dvd
  have h_pow_dvd : (7 : ℤ) ^ (l + 1) ∣ ((2 : ℤ) ^ d - 1) := by
    set n := d / 3 with hn_def
    have hd3 : d = 3 * n := by omega
    have h_rewrite : (2 : ℤ) ^ d - 1 = (8 : ℤ) ^ n - 1 ^ n := by
      rw [one_pow, show (8 : ℤ) = 2 ^ 3 from by norm_num, ← pow_mul, ← hd3]
    rw [h_rewrite]
    have h_l_dvd_n : 7 ^ l ∣ n := by
      have h_dvd_d : 7 ^ l ∣ d := pow_padicValNat_dvd
      rw [hd3] at h_dvd_d
      exact ((Nat.Coprime.pow_right l (by decide : Nat.Coprime 3 7)).symm.dvd_mul_left).mp h_dvd_d
    apply pow_dvd_of_le_emultiplicity
    have h_lte := Int.emultiplicity_pow_sub_pow (p := 7)
      (by decide : Nat.Prime 7) (by decide : Odd 7)
      (show (7 : ℤ) ∣ 8 - 1 from ⟨1, by norm_num⟩)
      (show ¬ (7 : ℤ) ∣ 8 from by decide)
      n
    rw [show (8 : ℤ) - 1 = (7 : ℤ) from by norm_num] at h_lte
    have h_em_n : (l : ℕ∞) ≤ emultiplicity (7 : ℕ) n :=
      le_emultiplicity_of_pow_dvd h_l_dvd_n
    have h_em_7 : (1 : ℕ∞) ≤ emultiplicity (↑(7 : ℕ)) ((7 : ℤ)) :=
      le_emultiplicity_of_pow_dvd (dvd_refl (7 : ℤ))
    calc (↑(l + 1) : ℕ∞) = 1 + ↑l := by push_cast; ring
      _ ≤ emultiplicity (↑(7 : ℕ)) (7 : ℤ) + emultiplicity (7 : ℕ) n :=
          add_le_add h_em_7 h_em_n
      _ = emultiplicity (↑(7 : ℕ)) ((8 : ℤ) ^ n - (1 : ℤ) ^ n) := h_lte.symm
  obtain ⟨h_Bd_div, h_Bd_ndiv⟩ := h_val
  obtain ⟨h_Ad_div, _⟩ := h_even_val
  have h_dvd_prod : (7 : ℤ) ^ (l + 1) ∣ P * binomialB d := by
    rw [h_identity]
    have h1 : (7 : ℤ) ^ (l + 1) ∣ 7 * binomialA' d := by
      rw [show (7 : ℤ) ^ (l + 1) = 7 * 7 ^ l from by rw [pow_succ, mul_comm]]
      exact mul_dvd_mul_left 7 h_Ad_div
    have h2 : (1 : ℤ) - 7 * binomialA' d - (2 : ℤ) ^ d =
        -(7 * binomialA' d + ((2 : ℤ) ^ d - 1)) := by ring
    rw [h2]
    exact dvd_neg.mpr (dvd_add h1 h_pow_dvd)
  have h_coprime : IsCoprime ((7 : ℤ) ^ (l + 1)) P := by
    apply IsCoprime.pow_left
    have hp : Prime (7 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
    exact (Prime.coprime_iff_not_dvd hp).mpr hP_coprime
  exact h_Bd_ndiv (h_coprime.dvd_of_dvd_mul_left h_dvd_prod)

/-- m = 3 is a solution: x = 5, (25+7)/4 = 8 = 2³. -/
lemma theta_eq_at_3 : -2 * θ + 1 = θ ^ 3 - θ' ^ 3 := by
  have h_div : ((5 : ℤ) ^ 2 + 7) / 4 = 2 ^ 3 := by norm_num
  exact main_m_condition 5 3 ⟨1, by omega⟩ (by omega) h_div

lemma theta_eq_at_5 : -2 * θ + 1 = θ ^ 5 - θ' ^ 5 := by
  have h_div : ((11 : ℤ) ^ 2 + 7) / 4 = 2 ^ 5 := by norm_num
  exact main_m_condition 11 5 ⟨2, by omega⟩ (by omega) h_div

lemma theta_eq_at_13 : -2 * θ + 1 = θ ^ 13 - θ' ^ 13 := by
  have h_div : ((181 : ℤ) ^ 2 + 7) / 4 = 2 ^ 13 := by norm_num
  exact main_m_condition 181 13 ⟨6, by omega⟩ (by omega) h_div

/-- For x² + 7 = 2ⁿ with odd n ≥ 5: n ∈ {5, 7, 15}. -/
theorem odd_case_only_three_values :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    n = 5 ∨ n = 7 ∨ n = 15 := by
  intro x n hn_odd hn_ge h_eq
  have h_mod := odd_case_only_three_values_mod_42 x n hn_odd hn_ge h_eq
  set m := n - 2 with hm_def
  have hm_odd : Odd m := by
    obtain ⟨k, hk⟩ := hn_odd
    refine ⟨k - 1, ?_⟩
    omega
  have hm_ge : m ≥ 3 := by omega
  have h_div := reduction_divide_by_4 x n hn_odd hn_ge h_eq
  have h_theta := main_m_condition x m hm_odd hm_ge h_div
  rcases h_mod with h3 | h5 | h13
  · left
    have : m = 3 := (at_most_one_m_per_class 3 m (by decide) hm_odd
      (by omega) hm_ge (by omega) theta_eq_at_3 h_theta).symm
    omega
  · right; left
    have : m = 5 := (at_most_one_m_per_class 5 m (by decide) hm_odd
      (by omega) hm_ge (by omega) theta_eq_at_5 h_theta).symm
    omega
  · right; right
    have : m = 13 := (at_most_one_m_per_class 13 m (by decide) hm_odd
      (by omega) hm_ge (by omega) theta_eq_at_13 h_theta).symm
    omega

lemma sq_odd_then_odd :
  ∀ (x : ℤ), Odd (x ^ 2) → Odd (x) := by
  simp [parity_simps]

lemma two_pow_min_seven_odd :
  ∀ (n : ℕ), n ≠ 0 → Odd ( (2 : ℤ) ^ n - 7 ) := by
  intro n hn
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have h_even : Even ((2 : ℤ) ^ n) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn'
    rw [hm, add_comm, pow_add, pow_one, mul_comm]
    exact even_two_mul ((2 : ℤ) ^ m)
  obtain ⟨k, hk⟩ := h_even
  use k - 4
  omega

lemma x_is_odd :
  ∀ x : ℤ, ∀ n : ℕ, n ≠ 0 → x ^ 2 + 7 = 2 ^ n →
    x % 2 = 1 := by
    intros x n hn h
    rw [← Int.odd_iff]
    refine sq_odd_then_odd x ?_
    rw [eq_tsub_of_add_eq h]
    exact two_pow_min_seven_odd n hn

lemma ramanujan_nagell_even_pow_factors :
  ∀ x : ℤ , ∀ k : ℕ, (2^k + x) * (2^k - x) = 7 →
    (2^k - x = 1 ∧ 2^k + x = 7) ∨ (2^k - x = 7 ∧ 2^k + x = 1) := by
  intro x k h
  have h_pos : (0 : ℤ) < 2 ^ k := by positivity
  have h_prod_pos : (2^k + x) * (2^k - x) > 0 := by rw [h]; norm_num
  have h_both_pos : 2^k + x > 0 ∧ 2^k - x > 0 := by
    constructor <;> nlinarith [mul_pos_iff.mp h_prod_pos]
  set a := 2^k + x with ha_def
  set b := 2^k - x with hb_def
  have hab : a * b = 7 := h
  have ha_pos : a > 0 := h_both_pos.1
  have hb_pos : b > 0 := h_both_pos.2
  have ha_le : a ≤ 7 := by nlinarith
  have hb_le : b ≤ 7 := by nlinarith
  have h_cases : (a = 1 ∧ b = 7) ∨ (a = 7 ∧ b = 1) := by
    rcases (show a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 by omega) with
      ha' | ha' | ha' | ha' | ha' | ha' | ha' <;> rw [ha'] at hab ⊢ <;> omega
  rcases h_cases with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
  · exact Or.inr ⟨hb_eq, ha_eq⟩
  · exact Or.inl ⟨hb_eq, ha_eq⟩

lemma helper_1
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 9) (h₂ : n = 4) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h₁ : x = 3 ∨ x = -3) with h | h <;>
      subst h h₂ <;> tauto

lemma helper_2
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 1) (h₂ : n = 3) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h₁ : x = 1 ∨ x = -1) with h | h <;>
      subst h h₂ <;> tauto

lemma helper_3
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 25) (h₂ : n = 5) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h₁ : x = 5 ∨ x = -5) with h | h <;>
      subst h h₂ <;> tauto

lemma helper_4
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 121) (h₂ : n = 7) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h₁ : x = 11 ∨ x = -11) with h | h <;>
      subst h h₂ <;> tauto

lemma helper_5
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 32761) (h₂ : n = 15) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h₁ : x = 181 ∨ x = -181) with h | h <;>
      subst h h₂ <;> tauto

end RamanujanNagell

open RamanujanNagell

/-- The Ramanujan-Nagell theorem. -/
theorem RamanujanNagell :
  ∀ x : ℤ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n →
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
  intro x n h
  have n_ge_3 : n ≥ 3 := by
    by_contra h_lt
    push Not at h_lt
    have h_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have h_pow_bound : (2 : ℤ) ^ n ≤ 4 := by
      match n with
      | 0 => norm_num
      | 1 => norm_num
      | 2 => norm_num
      | n + 3 => omega
    linarith
  have h₂ : x % 2 = 1 :=
    x_is_odd x n (by rintro rfl; simp only [pow_zero] at h; nlinarith [sq_nonneg x]) h
  rw [← Int.odd_iff] at h₂
  rcases Nat.even_or_odd n with h₃ | h₃
  · rcases exists_eq_mul_right_of_dvd (even_iff_two_dvd.mp h₃) with ⟨k, hk⟩
    rw [hk] at h
    have h₄ : (2^k + x) * (2^k - x) = 7 := by
      have : (2:ℤ)^(2*k) = 2^k * 2^k := by rw [two_mul, pow_add]
      linear_combination -h - this
    have h₄' := ramanujan_nagell_even_pow_factors x k h₄
    have h₅ : (8 : ℤ) = (2 : ℤ) * (2 : ℤ) ^ k := by
      rcases h₄' with ⟨h₄a, h₄b⟩ | ⟨h₄a, h₄b⟩ <;> linarith
    have h₆ : 2 ^ k = 4 := by linarith
    have k_eq_2 : k = 2 := by
      have h₇ : 4 = 2 ^ 2 := by norm_num
      rw [h₇] at h₆
      exact Nat.pow_right_injective (by norm_num) h₆
    have n_eq_4 : n = 4 := by linarith
    refine helper_1 ?_ n_eq_4
    rw [k_eq_2] at h; norm_num at h; linarith
  · have m := Nat.le.dest n_ge_3
    rcases m with _ | m
    · have n_eq_3 : n = 3 := by linarith
      refine helper_2 ?_ n_eq_3
      rw [n_eq_3] at h; norm_num at h; linarith
    · have n_ge_5 : n ≥ 5 := by rcases h₃ with ⟨j, hj⟩; omega
      have h_cases := odd_case_only_three_values x n h₃ n_ge_5 (by linarith : x ^ 2 + 7 = 2 ^ n)
      rcases h_cases with hn5 | hn7 | hn15
      · refine helper_3 ?_ hn5
        rw [hn5] at h; norm_num at h; linarith
      · refine helper_4 ?_ hn7
        rw [hn7] at h; norm_num at h; linarith
      · refine helper_5 ?_ hn15
        rw [hn15] at h; norm_num at h; linarith

/-- Exact iff form of the Ramanujan-Nagell theorem: the integer solutions of
    `x ^ 2 + 7 = 2 ^ n` are precisely `(±1, 3)`, `(±3, 4)`,
    `(±5, 5)`, `(±11, 7)`, and `(±181, 15)`. -/
theorem ramanujanNagellExact :
  ∀ x : ℤ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n ↔
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
  intro x n
  constructor
  · exact RamanujanNagell x n
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h <;>
      (rw [Prod.mk.injEq] at h; obtain ⟨hx, hn⟩ := h; subst hx; subst hn; norm_num)
