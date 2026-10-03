/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Interfaces
public import LeanPool.Zeta32.Arith.Sum.Main

/-! The arithmetic node (the proof notes, §8 opening and §9): from the per-prime bounds
(taken as hypotheses) and `ArithSum.arith_sum`,
`∀ ε > 0, ∀ᶠ n, Q r n ≠ 0 → log d_n ≤ (283/50 + ε) n²`.

Bridge: for `Q r n ≠ 0`, `P = d Q` is primitive, so `v_p(d) = −min_k v_p(Q_k) = cost r n p`
for every
prime `p`, and `log d = Σ_p v_p(d) log p` over any finite set of primes containing the
support. Primes
`p > 5n` have `cost ≤ 0` (large-prime integrality; for `n ≥ den r` no such prime divides `den r`).
For `Q r n = 0` the definition of `cost` is irrelevant (the conclusion is vacuous); `arith_sum`
is applied to
`costQ`, which equals `cost` when `Q r n ≠ 0` and is below every hypothesis bound when `Q r n =
0`. -/

public section

open Polynomial Filter Topology
open scoped BigOperators

namespace Zeta32
namespace Arith
noncomputable section

/-! ### Logarithm of a positive rational as a finite prime sum -/

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/RationalPrimeSupport.lean
/-- Prime divisors of the numerator or denominator of a rational number. -/
def ratPrimeSupport (s : ℚ) : Finset ℕ :=
  s.num.natAbs.factorization.support ∪ s.den.factorization.support

theorem ratPrimeSupport_prime {s : ℚ} {p : ℕ}
    (hp : p ∈ ratPrimeSupport s) : p.Prime := by
  change p ∈ s.num.natAbs.factorization.support ∪ s.den.factorization.support at hp
  rcases Finset.mem_union.mp hp with hn | hd
  · exact Nat.prime_of_mem_primeFactors (n := s.num.natAbs) (by simpa using hn)
  · exact Nat.prime_of_mem_primeFactors (n := s.den) (by simpa using hd)

theorem padicValRat_eq_factorizations (p : ℕ) (hp : p.Prime) (s : ℚ) :
    padicValRat p s =
      (s.num.natAbs.factorization p : ℤ) - (s.den.factorization p : ℤ) := by
  rw [padicValRat_def]
  change (padicValNat p s.num.natAbs : ℤ) - (padicValNat p s.den : ℤ) = _
  rw [← Nat.factorization_def s.num.natAbs hp,
    ← Nat.factorization_def s.den hp]

theorem padicValRat_eq_zero_of_not_mem_ratPrimeSupport {s : ℚ} {p : ℕ}
    (hp : p.Prime) (hnot : p ∉ ratPrimeSupport s) : padicValRat p s = 0 := by
  change p ∉ s.num.natAbs.factorization.support ∪ s.den.factorization.support at hnot
  have hn : s.num.natAbs.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hnot (Finset.mem_union.mpr (Or.inl h)))
  have hd : s.den.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hnot (Finset.mem_union.mpr (Or.inr h)))
  rw [padicValRat_eq_factorizations p hp s, hn, hd]
  simp

-- adapted from dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/RationalPrimeLog.lean
theorem log_nat_eq_sum_of_support_subset (n : ℕ) (S : Finset ℕ)
    (hS : n.factorization.support ⊆ S) :
    Real.log (n : ℝ) =
      ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ n.factorization.support,
    (n.factorization p : ℝ) * Real.log (p : ℝ)) = _
  apply Finset.sum_subset hS
  intro p hpS hpout
  rw [Finsupp.notMem_support_iff.mp hpout]
  simp

theorem log_rat_eq_sum_padicValRat {s : ℚ} (hs : 0 < s) :
    Real.log (s : ℝ) =
      ∑ p ∈ ratPrimeSupport s, (padicValRat p s : ℝ) * Real.log (p : ℝ) := by
  have hnum : 0 < s.num := Rat.num_pos.mpr hs
  have hnum0 : (s.num : ℝ) ≠ 0 := (Int.cast_pos.mpr hnum).ne'
  have hden0 : (s.den : ℝ) ≠ 0 := (Nat.cast_pos.mpr s.den_pos).ne'
  have habs : (s.num.natAbs : ℝ) = (s.num : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnum.le)
    simpa only [Int.cast_natCast] using h
  have hN : s.num.natAbs.factorization.support ⊆ ratPrimeSupport s := by
    intro p hp
    exact Finset.mem_union.mpr (Or.inl hp)
  have hD : s.den.factorization.support ⊆ ratPrimeSupport s := by
    intro p hp
    exact Finset.mem_union.mpr (Or.inr hp)
  calc
    Real.log (s : ℝ) =
        Real.log (s.num.natAbs : ℝ) - Real.log (s.den : ℝ) := by
      rw [Rat.cast_def, Real.log_div hnum0 hden0, habs]
    _ = (∑ p ∈ ratPrimeSupport s,
          (s.num.natAbs.factorization p : ℝ) * Real.log (p : ℝ)) -
        (∑ p ∈ ratPrimeSupport s,
          (s.den.factorization p : ℝ) * Real.log (p : ℝ)) := by
      rw [log_nat_eq_sum_of_support_subset s.num.natAbs (ratPrimeSupport s) hN,
        log_nat_eq_sum_of_support_subset s.den (ratPrimeSupport s) hD]
    _ = ∑ p ∈ ratPrimeSupport s,
        (padicValRat p s : ℝ) * Real.log (p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [padicValRat_eq_factorizations p (ratPrimeSupport_prime hp) s,
        Int.cast_sub, Int.cast_natCast, sub_mul]

theorem log_rat_eq_sum_padicValRat_of_support_subset {s : ℚ} (hs : 0 < s)
    (S : Finset ℕ) (hS : ratPrimeSupport s ⊆ S)
    (hprime : ∀ p ∈ S, p.Prime) :
    Real.log (s : ℝ) =
      ∑ p ∈ S, (padicValRat p s : ℝ) * Real.log (p : ℝ) := by
  rw [log_rat_eq_sum_padicValRat hs]
  apply Finset.sum_subset hS
  intro p hp hpout
  rw [padicValRat_eq_zero_of_not_mem_ratPrimeSupport (hprime p hp) hpout]
  simp

/-! ### Primitive content: `v_p(d) = −min_k v_p(Q_k)` -/

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/PrimitiveReduction.lean
lemma primitive_exists_coeff_not_dvd (p : ℕ) [hp : Fact p.Prime] (T : ℤ[X]) (hT : T.IsPrimitive) :
    ∃ k, ¬(p:ℤ) ∣ T.coeff k := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hu := hT (p:ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr h)
  exact (Nat.prime_iff_prime_int.mp hp.out).not_isUnit hu

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/PrimitiveCoefficientMinimum.lean
theorem primitive_scale_coeff_valuation_minimum (p : ℕ) [Fact p.Prime]
    (T : ℤ[X]) (hT : T.IsPrimitive) (F : ℚ[X]) (s : ℚ) (hs : s ≠ 0)
    (hprop : T.map (algebraMap ℤ ℚ) = C s * F) :
    ∃ k, F.coeff k ≠ 0 ∧ padicValRat p (F.coeff k) = -padicValRat p s ∧
      ∀ j, F.coeff j ≠ 0 → padicValRat p (F.coeff k) ≤ padicValRat p (F.coeff j) := by
  have hcoeff (k : ℕ) : (T.coeff k : ℚ) = s * F.coeff k := by
    have h := congrArg (fun f : ℚ[X] => f.coeff k) hprop
    simpa only [coeff_map, coeff_C_mul] using! h
  obtain ⟨k, hk⟩ := primitive_exists_coeff_not_dvd p T hT
  have hkF : F.coeff k ≠ 0 := by
    intro hz
    have hTq : (T.coeff k : ℚ) = 0 := by rw [hcoeff k, hz, mul_zero]
    have hTz : T.coeff k = 0 := by exact_mod_cast hTq
    exact hk (by rw [hTz]; exact dvd_zero _)
  have hkT : padicValRat p (T.coeff k : ℚ) = 0 := by
    simp only [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hk, Nat.cast_zero]
  have hkval := padicValRat.mul (p := p) hs hkF
  rw [← hcoeff k, hkT] at hkval
  have hke : padicValRat p (F.coeff k) = -padicValRat p s := by omega
  refine ⟨k, hkF, hke, ?_⟩
  intro j hj
  have hjnonneg : 0 ≤ padicValRat p (T.coeff j : ℚ) := by
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg _
  rw [hcoeff j, padicValRat.mul hs hj] at hjnonneg
  omega

theorem Qtilde_ne_zero (r : ℚ) (n : ℕ) (hQ : Q r n ≠ 0) : Qtilde r n ≠ 0 := by
  unfold Qtilde
  exact mul_ne_zero (by simpa using (scale_pos n).ne') hQ

theorem P_isPrimitive (r : ℚ) (n : ℕ) (hQ : Q r n ≠ 0) : (P r n).IsPrimitive := by
  have h := primitiveQ_isPrimitive r n hQ
  unfold P
  split_ifs
  · exact h
  · intro c hc
    exact h c ((dvd_neg).mp hc)

/-- For `Q r n ≠ 0`, `cost r n p = v_p(d)`. -/
theorem cost_eq_padicValRat_dtilde (r : ℚ) (n p : ℕ) (hp : p.Prime) (hQ : Q r n ≠ 0) :
    cost r n p = (padicValRat p (dtilde r n) : ℝ) := by
  have := Fact.mk hp
  obtain ⟨k, hk, hkv, hmin⟩ := primitive_scale_coeff_valuation_minimum p (P r n)
    (P_isPrimitive r n hQ) (Qtilde r n) (dtilde r n) (dtilde_pos r n).ne' (P_eq_dtilde_Qtilde r n)
  have hleast : IsLeast {v : ℝ | ∃ k, (Qtilde r n).coeff k ≠ 0 ∧
      v = (padicValRat p ((Qtilde r n).coeff k) : ℝ)} (padicValRat p ((Qtilde r n).coeff k) : ℝ)
        := by
    refine ⟨⟨k, hk, rfl⟩, ?_⟩
    rintro v ⟨j, hj, rfl⟩
    exact_mod_cast hmin j hj
  unfold cost
  rw [hleast.csInf_eq, hkv]
  push_cast
  ring

/-- A uniform lower bound on the coefficient valuations bounds `cost` from above. -/
theorem cost_le_of_forall (r : ℚ) (n p : ℕ) (hQ : Q r n ≠ 0) (b : ℝ)
    (h : ∀ k, (Qtilde r n).coeff k ≠ 0 → b ≤ (padicValRat p ((Qtilde r n).coeff k) : ℝ)) :
    cost r n p ≤ -b := by
  obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr (Qtilde_ne_zero r n hQ)
  have hne : ({v : ℝ | ∃ k, (Qtilde r n).coeff k ≠ 0 ∧
      v = (padicValRat p ((Qtilde r n).coeff k) : ℝ)}).Nonempty :=
    ⟨_, k, Polynomial.mem_support_iff.mp hk, rfl⟩
  have hinf := le_csInf hne (by rintro v ⟨j, hj, rfl⟩; exact h j hj)
  unfold cost
  linarith

/-- For `Q r n ≠ 0` and `cost ≤ 0` beyond `5n`: `log d ≤ Σ_{p ≤ 5n} cost_p log p`. -/
theorem log_dtilde_le_sum (r : ℚ) (n : ℕ) (hQ : Q r n ≠ 0)
    (hlarge : ∀ p : ℕ, p.Prime → 5 * n < p → cost r n p ≤ 0) :
    Real.log (dtilde r n) ≤
      ∑ p ∈ (Finset.range (5 * n + 1)).filter Nat.Prime, cost r n p * Real.log p := by
  set S := ratPrimeSupport (dtilde r n) ∪ (Finset.range (5 * n + 1)).filter Nat.Prime with hSdef
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact ratPrimeSupport_prime h
    · exact (Finset.mem_filter.mp h).2
  rw [log_rat_eq_sum_padicValRat_of_support_subset (dtilde_pos r n) S Finset.subset_union_left
    hSprime,
    ← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ 5 * n)]
  have hfilt : S.filter (fun p => p ≤ 5 * n) = (Finset.range (5 * n + 1)).filter Nat.Prime := by
    ext p
    simp only [hSdef, Finset.mem_filter, Finset.mem_union, Finset.mem_range]
    constructor
    · rintro ⟨h | h, hp⟩
      · exact ⟨by omega, ratPrimeSupport_prime h⟩
      · exact ⟨h.1, h.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr ⟨h1, h2⟩, by omega⟩
  rw [hfilt]
  have h1 : ∑ p ∈ (Finset.range (5 * n + 1)).filter Nat.Prime,
      (padicValRat p (dtilde r n) : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (5 * n + 1)).filter Nat.Prime, cost r n p * Real.log p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [cost_eq_padicValRat_dtilde r n p (Finset.mem_filter.mp hp).2 hQ]
  have h2 : ∑ p ∈ S.filter (fun p => ¬ p ≤ 5 * n),
      (padicValRat p (dtilde r n) : ℝ) * Real.log p ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    obtain ⟨hpS, hp5⟩ := Finset.mem_filter.mp hp
    have hpp := hSprime p hpS
    rw [← cost_eq_padicValRat_dtilde r n p hpp hQ]
    exact mul_nonpos_of_nonpos_of_nonneg (hlarge p hpp (by omega))
      (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
  linarith

/-! ### The node -/

/-- `cost`, patched on `Q r n = 0` (where the conclusion of the node is vacuous) to lie below every
per-prime bound. -/
def costQ (r : ℚ) (n p : ℕ) : ℝ :=
  if Q r n = 0 then
    min ((n : ℝ) * ArithSum.psiL ((p : ℝ) / (n : ℝ)) + 3 / 4)
      (min ((n : ℝ) * ArithSum.phiL ((p : ℝ) / (n : ℝ)) + 5) 0)
  else cost r n p

lemma rpow_third {x : ℝ} (hx : 0 < x) :
    x ^ (2 / 3 : ℝ) = (x ^ (1 / 3 : ℝ)) ^ 2 ∧ x = (x ^ (1 / 3 : ℝ)) ^ 3 := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

theorem arith_of_parts : ∀ r : ℚ,
    (∀ᶠ n : ℕ in atTop, ∀ p : ℕ, p.Prime → (n:ℝ)^(2/3:ℝ) < p → p ≤ 5*n → ¬ p ∣ r.den →
      GreedyBound r n p) →
    (∀ (n p : ℕ), p.Prime → 7 ≤ p → 5*n < p^2 → Q r n ≠ 0 → 3*p ≤ 7*n →
      GreedyBound r n p → cost r n p ≤ n * ArithSum.psiL ((p:ℝ)/(n:ℝ)) + 3/4) →
    (∀ᶠ n : ℕ in atTop, ∀ p : ℕ, p.Prime → 7*n < 3*p → p ≤ 5*n → ¬ p ∣ r.den →
      Q r n ≠ 0 → cost r n p ≤ n * ArithSum.phiL ((p:ℝ)/(n:ℝ)) + 5) →
    (∀ (n p : ℕ), p.Prime → 5*n < p → ¬ p ∣ r.den → ∀ k,
      (Qtilde r n).coeff k ≠ 0 → 0 ≤ padicValRat p ((Qtilde r n).coeff k)) →
    (∀ (n p : ℕ), p.Prime → ∀ k, (Qtilde r n).coeff k ≠ 0 →
      padicValRat p ((Qtilde r n).coeff k) ≥ -3*(3*n)*Nat.log p (10*n+2) - (3*n)*padicValNat p
        r.den) →
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Q r n ≠ 0 → Real.log (dtilde r n) ≤ (283/50 + ε) * (n:ℝ)^2 := by
  intro r hE hF hG hL hK ε hε
  have hden := r.den_pos
  -- `h0` of `arith_sum`
  have h0 : ∀ (n p : ℕ), p.Prime →
      costQ r n p ≤ 9*n*Nat.log p (10*n+2) + 3*n*padicValNat p r.den := by
    intro n p hp
    by_cases hQ : Q r n = 0
    · simp only [costQ, hQ, ↓reduceIte]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (by positivity))
    · simp only [costQ, hQ, ↓reduceIte]
      have h := cost_le_of_forall r n p hQ
        (-(9*n*Nat.log p (10*n+2) + 3*n*padicValNat p r.den : ℝ)) (fun k hk => by
          have h1 := hK n p hp k hk
          have h2 : ((-3*(3*n)*Nat.log p (10*n+2) - (3*n)*padicValNat p r.den : ℤ) : ℝ) ≤
              (padicValRat p ((Qtilde r n).coeff k) : ℝ) := by exact_mod_cast h1
          simp only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_ofNat]
            at h2
          linarith)
      linarith
  -- `h1` of `arith_sum`
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hbig := ht.eventually (eventually_ge_atTop (max 7 (r.den : ℝ)))
  have h1 : ∀ᶠ (n : ℕ) in atTop, ∀ (p : ℕ), p.Prime → (n:ℝ)^(2/3:ℝ) < p → 3*p ≤ 7*n →
      costQ r n p ≤ n * ArithSum.psiL ((p:ℝ)/(n:ℝ)) + 3/4 := by
    filter_upwards [hE, hbig, eventually_ge_atTop 1] with n hEn hbn hn1
    intro p hp hlow h3
    by_cases hQ : Q r n = 0
    · simp only [costQ, hQ, ↓reduceIte]
      exact min_le_left _ _
    · simp only [costQ, hQ, ↓reduceIte]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      obtain ⟨ht2, ht3⟩ := rpow_third hn0
      have hlow' := hlow
      rw [ht2] at hlow'
      set t := (n : ℝ) ^ (1 / 3 : ℝ) with htdef
      have ht7 : 7 ≤ t := le_trans (le_max_left _ _) hbn
      have htd : (r.den : ℝ) ≤ t := le_trans (le_max_right _ _) hbn
      have htt : t ≤ t ^ 2 := by nlinarith
      have hp7R : (7 : ℝ) < p := by linarith
      have hp7 : 7 ≤ p := by exact_mod_cast hp7R.le
      have hpd : ¬ p ∣ r.den := by
        intro hd
        have hle : (p : ℝ) ≤ r.den := by exact_mod_cast Nat.le_of_dvd hden hd
        linarith
      have hp5 : p ≤ 5 * n := by omega
      have hsq : 5 * n < p ^ 2 := by
        have ht0 : 0 ≤ t ^ 2 := sq_nonneg t
        have hA : (t ^ 2) ^ 2 < (p : ℝ) ^ 2 := pow_lt_pow_left₀ hlow' ht0 (by norm_num)
        have hB : (t ^ 2) ^ 2 = t * (n : ℝ) := by rw [ht3]; ring
        have hC : (5 : ℝ) * n < p ^ 2 := by nlinarith
        exact_mod_cast hC
      exact hF n p hp hp7 hsq hQ h3 (hEn p hp hlow hp5 hpd)
  -- `h2` of `arith_sum`
  have h2 : ∀ᶠ (n : ℕ) in atTop, ∀ (p : ℕ), p.Prime → 7*n < 3*p → p ≤ 5*n →
      costQ r n p ≤ n * ArithSum.phiL ((p:ℝ)/(n:ℝ)) + 5 := by
    filter_upwards [hG, eventually_ge_atTop r.den] with n hGn hnd
    intro p hp h7 h5
    by_cases hQ : Q r n = 0
    · simp only [costQ, hQ, ↓reduceIte]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · simp only [costQ, hQ, ↓reduceIte]
      have hpd : ¬ p ∣ r.den := by
        intro hd
        have := Nat.le_of_dvd hden hd
        omega
      exact hGn p hp h7 h5 hpd hQ
  have hsum := ArithSum.arith_sum (costQ r) r.den hden h0 h1 h2 ε hε
  filter_upwards [hsum, eventually_ge_atTop r.den] with n hn hnd hQ
  have hlarge : ∀ p : ℕ, p.Prime → 5 * n < p → cost r n p ≤ 0 := by
    intro p hp hp5
    have hpd : ¬ p ∣ r.den := by
      intro hd
      have := Nat.le_of_dvd hden hd
      omega
    have h := cost_le_of_forall r n p hQ 0 (fun k hk => by exact_mod_cast hL n p hp hp5 hpd k hk)
    simpa using h
  have hlog := log_dtilde_le_sum r n hQ hlarge
  have heq : ∑ p ∈ (Finset.range (5 * n + 1)).filter Nat.Prime, costQ r n p * Real.log p =
      ∑ p ∈ (Finset.range (5 * n + 1)).filter Nat.Prime, cost r n p * Real.log p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [costQ, hQ, ↓reduceIte]
  linarith

end
end Arith
end Zeta32

end
