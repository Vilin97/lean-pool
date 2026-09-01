/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Order.Field.Power
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

import LeanPool.QuadraticIterates.ArchMath1992.DegreeCriterion

/-!
# The main theorems

The integer factors `b_n` of the `c`-sequence — integral, pairwise coprime, and recovering `c_n` by
Möbius inversion (Lemma 1.1 b) — and the three results of the paper: `section1_equiv`
(`Ω_n ≅ [C₂]ⁿ` iff the `c_i` are 2-independent iff the `b_i` are), `section1_squarefree` (no
`|b_k|` a square forces `Ω_n ≅ [C₂]ⁿ`) and `section3_main` (the congruence conditions on `a` that
guarantee this for every `n`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

open Polynomial
open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

section

variable (a : ℤ)

/-! ### The integer factors `b_n` -/

lemma cSeq_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) : cSeq a n ≠ 0 := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by lia
    have ha0 := ne_zero_of_not_isSquare_neg a ha
    simpa using ha0
  · exact (cSeq_pos a ha h2).ne'

/-- `cSeq_ne_zero` in the `∀ d ≥ 1` form the `moebiusFactorR` API consumes. -/
private lemma cSeq_ne_zero' (ha : ¬IsSquare (-a : ℚ)) : ∀ d ≥ 1, cSeq a d ≠ 0 :=
  fun _ ↦ cSeq_ne_zero a ha

/-- The constant-valuation shape for `c`: the specialization of `factorization_gammaSeq_shape`
to `X² + a`, `ε = -1`, in the form consumed by `moebiusFactorR_isRelPrime`. -/
lemma cSeq_factorization_shape (ha : ¬IsSquare (-a : ℚ)) :
    ∀ q : ℤ, Prime q → normalize q = q →
      ∃ m ≥ 1, ∃ E : ℕ, ∀ k ≥ 1, factorization (cSeq a k) q = if m ∣ k then E else 0 :=
  fun _ hq hqn ↦ factorization_gammaSeq_shape (evenPoly_X_sq_add_C a) (by norm_num)
    (cSeq_ne_zero' a ha) hq hqn

/-- The image of `b_n` in `ℚ` is the Möbius product `∏_{ed = n} c_d^{μ(e)}` (Lemma 1.1 b): the
Möbius product of the `c`-sequence is the integer `b_n`, since `c` is a strong divisibility
sequence. -/
lemma intCast_bSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    (bSeq a n : ℚ) = moebiusFactor (cSeq a) n := by
  rw [bSeq_eq_moebiusFactorR]
  exact intCast_moebiusFactorR (cSeq_ne_zero' a ha) (cSeq_gcd a) hn

lemma bSeq_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) : bSeq a n ≠ 0 := by
  rw [bSeq_eq_moebiusFactorR]
  exact moebiusFactorR_ne_zero (cSeq_ne_zero' a ha) (cSeq_associated_gcd a) n hn

/-- Möbius inversion for the integer factors (Lemma 1.1 b): `c_n = ∏_{d ∣ n} b_d`. -/
lemma cSeq_eq_prod_bSeq (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n) :
    cSeq a n = ∏ d ∈ n.divisors, bSeq a d := by
  simp only [bSeq_eq_moebiusFactorR]
  exact prod_moebiusFactorR (cSeq_ne_zero' a ha) (cSeq_associated_gcd a) n hn

/-- The integer factors `b_n` are pairwise coprime (Lemma 1.1 b): the valuation of `b_n` at
each prime is supported on a single index, so no prime divides two distinct factors. -/
lemma isCoprime_bSeq (ha : ¬IsSquare (-a : ℚ)) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≠ n) : IsCoprime (bSeq a m) (bSeq a n) := by
  rw [bSeq_eq_moebiusFactorR, bSeq_eq_moebiusFactorR]
  exact (moebiusFactorR_isRelPrime (cSeq_ne_zero' a ha) (cSeq_associated_gcd a)
    (cSeq_factorization_shape a ha) m n hm hn hmn).isCoprime

end

section

variable (a : ℤ)

/-! ### The main theorems -/

lemma nonempty_mulEquiv_of_finrank_eq {n : ℕ}
    (hmax : Module.finrank ℚ ↥(splittingField a n) = 2 ^ (2 ^ n - 1)) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) := by
  obtain ⟨φ, hφ⟩ := odoni_embedding a n
  have hfinG : Finite (GaloisGroup a n) :=
    Nat.finite_of_card_ne_zero (by rw [card_galoisGroup_eq_finrank a n, hmax]; positivity)
  have hfinW : Finite (WreathPower n) :=
    Nat.finite_of_card_ne_zero (by rw [card_wreathPower]; positivity)
  exact (MonoidHom.nonempty_mulEquiv_iff_card_eq φ hφ).mpr
    (by rw [card_galoisGroup_eq_finrank a n, hmax, card_wreathPower])

/-- Section 1, `(a) ↔ (b)`: `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are 2-independent. -/
theorem section1_a_iff_b (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) ↔
      TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)) := by
  induction n with
  | zero =>
    refine ⟨fun _ ↦ ⟨fun i ↦ i.elim0, fun S hS ↦ hS.elim fun i _ ↦ i.elim0⟩, fun _ ↦ ?_⟩
    apply nonempty_mulEquiv_of_finrank_eq a
    rw [splittingField_zero_eq_bot, IntermediateField.finrank_bot]
    norm_num
  | succ n ih =>
    have hc0 : (cSeq a (n + 1) : ℚ) ≠ 0 := mod_cast cSeq_ne_zero a ha (by lia)
    have hsnoc : (fun i : Fin (n + 1) ↦ (cSeq a ((i : ℕ) + 1) : ℚ))
        = Fin.snoc (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)) (cSeq a (n + 1) : ℚ) := by
      ext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp [Fin.snoc_castSucc]
      · simp [Fin.snoc_last]
    rw [hsnoc, (embed_equiv a n).2]
    refine ⟨fun ⟨hiso, hrel⟩ ↦ ?_, fun hsnocindep ↦ ?_⟩
    · exact (kummer_extension_criterion a hiso (ih.mp hiso) hc0).mp
        ((degree_criterion a (irreducible_iteratedPoly a ha n)).mp hrel)
    · have hindep := TwoIndependent.of_snoc hsnocindep
      have hiso : Nonempty (GaloisGroup a n ≃* WreathPower n) := ih.mpr hindep
      exact ⟨hiso, (degree_criterion a (irreducible_iteratedPoly a ha n)).mpr
        ((kummer_extension_criterion a hiso hindep hc0).mpr hsnocindep)⟩

/-- In `ℚˣ/(ℚˣ)²`, the class of `c_m` is the sum of the classes of the `b_d` over `d ∣ m`. -/
lemma sqClass_cSeq_eq_sum_divisors (ha : ¬IsSquare (-a : ℚ)) {m : ℕ} (hm : 1 ≤ m) :
    sqClass (cSeq a m : ℚ) = ∑ d ∈ m.divisors, sqClass (bSeq a d : ℚ) := by
  have hprod : (cSeq a m : ℚ) = ∏ d ∈ m.divisors, (bSeq a d : ℚ) := by
    rw [cSeq_eq_prod_bSeq a ha hm]
    push_cast
    rfl
  rw [hprod, sqClass_prod fun d hd ↦
    mod_cast bSeq_ne_zero a ha (Nat.pos_of_mem_divisors hd)]

/-- In `ℚˣ/(ℚˣ)²`, the class of `b_m` is the Möbius-weighted sum of the classes of the `c_d`. -/
lemma sqClass_bSeq_eq_sum_divisorsAntidiagonal (ha : ¬IsSquare (-a : ℚ)) {m : ℕ} (hm : 1 ≤ m) :
    sqClass (bSeq a m : ℚ) = ∑ x ∈ m.divisorsAntidiagonal, (μ x.1) • sqClass (cSeq a x.2 : ℚ) := by
  rw [intCast_bSeq a ha hm, moebiusFactor_eq_prod, sqClass_prod_zpow _ fun x hx ↦
    mod_cast cSeq_ne_zero a ha
      (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx))]

/-- Section 1, `(b) ↔ (c)`: `c_1, …, c_n` are 2-independent iff `b_1, …, b_n` are 2-independent. -/
theorem section1_b_iff_c (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)) ↔
      TwoIndependent (fun i : Fin n ↦ (bSeq a ((i : ℕ) + 1) : ℚ)) := by
  have hmem (F : ℕ → ℚ) (d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n) :
      sqClass (F d) ∈ Set.range (fun j : Fin n ↦ sqClass (F ((j : ℕ) + 1))) :=
    ⟨⟨d - 1, by lia⟩, by simp [Nat.sub_add_cancel hd1]⟩
  have hspan :
      Submodule.span (ZMod 2) (Set.range fun i : Fin n ↦ sqClass (cSeq a ((i : ℕ) + 1) : ℚ))
        = Submodule.span (ZMod 2)
            (Set.range fun i : Fin n ↦ sqClass (bSeq a ((i : ℕ) + 1) : ℚ)) := by
    have hdvd {i : Fin n} {d : ℕ} (hd : d ∣ (i : ℕ) + 1) : 1 ≤ d ∧ d ≤ n :=
      ⟨Nat.pos_of_dvd_of_pos hd (by lia), (Nat.le_of_dvd (by lia) hd).trans (by have := i.2; lia)⟩
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      rw [SetLike.mem_coe, sqClass_cSeq_eq_sum_divisors a ha (by lia)]
      exact Submodule.sum_mem _ fun d hd ↦ Submodule.subset_span
        (hmem (fun k ↦ (bSeq a k : ℚ)) d (hdvd (Nat.dvd_of_mem_divisors hd)).1
          (hdvd (Nat.dvd_of_mem_divisors hd)).2)
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      rw [SetLike.mem_coe, sqClass_bSeq_eq_sum_divisorsAntidiagonal a ha (by lia)]
      refine Submodule.sum_mem _ fun x hx ↦ zsmul_mem (Submodule.subset_span ?_) (μ x.1)
      have hx2 := hdvd (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))
      exact hmem (fun d ↦ (cSeq a d : ℚ)) x.2 hx2.1 hx2.2
  rw [twoIndependent_iff_linearIndependent, twoIndependent_iff_linearIndependent,
    linearIndependent_iff_card_eq_finrank_span, linearIndependent_iff_card_eq_finrank_span,
    show (Set.range fun i : Fin n ↦ sqClass (cSeq a ((i : ℕ) + 1) : ℚ)).finrank (ZMod 2)
        = (Set.range fun i : Fin n ↦ sqClass (bSeq a ((i : ℕ) + 1) : ℚ)).finrank (ZMod 2) by
      simp only [Set.finrank]
      rw [hspan]]

/-- Theorem (Section 1), part 1: `Ω_n ≅ [C_2]^n` iff `c_1, …, c_n` are 2-independent iff
`b_1, …, b_n` are 2-independent. -/
theorem section1_equiv (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    [Nonempty (GaloisGroup a n ≃* WreathPower n),
     TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)),
     TwoIndependent (fun i : Fin n ↦ (bSeq a ((i : ℕ) + 1) : ℚ))].TFAE := by
  tfae_have 1 ↔ 2 := section1_a_iff_b a ha n
  tfae_have 2 ↔ 3 := section1_b_iff_c a ha n
  tfae_finish

/-- Theorem (Section 1), part 2: if none of `|b_2|, …, |b_n|` is a square in `ℚ`, then `Ω_n ≅
[C_2]^n`. -/
theorem section1_squarefree (ha : ¬IsSquare (-a : ℚ)) (n : ℕ)
    (h : ∀ k ≥ 2, k ≤ n → ¬IsSquare |bSeq a k|) :
    Nonempty (GaloisGroup a n ≃* WreathPower n) := by
  refine ((section1_equiv a ha n).out 2 0).mp ?_
  refine ⟨fun i ↦ by simpa using bSeq_ne_zero a ha (Nat.le_add_left 1 (i : ℕ)), fun S hS hsq ↦ ?_⟩
  have hsq_int : IsSquare (∏ i ∈ S, bSeq a ((i : ℕ) + 1)) := by
    rwa [show (∏ i ∈ S, (bSeq a ((i : ℕ) + 1) : ℚ))
        = ((∏ i ∈ S, bSeq a ((i : ℕ) + 1) : ℤ) : ℚ) by push_cast; rfl,
      Rat.isSquare_intCast_iff] at hsq
  have heach := Int.isSquare_abs_of_isSquare_prod_of_pairwise_isCoprime
    (fun i : Fin n ↦ bSeq a ((i : ℕ) + 1)) S
    (fun i _ j _ hij ↦ isCoprime_bSeq a ha (by lia) (by lia) fun hcon ↦ hij (Fin.ext (by lia)))
    hsq_int
  obtain ⟨i0, hi0⟩ := hS
  by_cases hexists : ∃ j ∈ S, 1 ≤ (j : ℕ)
  · obtain ⟨j, hjS, hj1⟩ := hexists
    exact h ((j : ℕ) + 1) (by lia) (by have := j.2; lia) (heach j hjS)
  · push Not at hexists
    have hi0z : (i0 : ℕ) = 0 := by have := hexists i0 hi0; lia
    have hSeq : S = {i0} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨⟨i0, hi0⟩, fun x hx ↦ Fin.ext (by have h1 := hexists x hx; have h2 := hi0z; lia)⟩
    rw [hSeq, Finset.prod_singleton] at hsq
    refine absurd ?_ ha
    have hb1eq : bSeq a ((i0 : ℕ) + 1) = -a := by rw [hi0z, zero_add, bSeq_one]
    rw [hb1eq] at hsq
    exact_mod_cast hsq

private lemma sign_eq_one_or_neg_one (ha0 : a ≠ 0) : a.sign = 1 ∨ a.sign = -1 :=
  (Int.sign_trichotomy a).elim Or.inl
    fun h ↦ h.elim (fun h0 ↦ (ha0 (Int.eq_zero_of_sign_eq_zero h0)).elim) Or.inr

/-- Induction core of `abs_cSeq_eq_gammaSeq_mul_abs`: for `d ≥ 2`, `γ_d · |a| = c_d`. -/
private lemma gammaSeq_mul_abs_eq_cSeq (hsignabs : a.sign * |a| = a)
    (hγ1 : gammaSeq (normPoly a) a.sign 1 = 1) {d : ℕ} (hd : 2 ≤ d) :
    gammaSeq (normPoly a) a.sign d * |a| = cSeq a d := by
  induction d with
  | zero => lia
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by lia
      rw [gammaSeq_succ _ a.sign le_rfl, hγ1, eval_normPoly, cSeq_two]
      linear_combination sq_abs a + hsignabs
    · rw [gammaSeq_succ _ a.sign (by lia), eval_normPoly, cSeq_succ a (by lia), add_mul, hsignabs,
        show |a| * gammaSeq (normPoly a) a.sign k ^ 2 * |a|
          = (gammaSeq (normPoly a) a.sign k * |a|) ^ 2 by ring, ih hk]

lemma abs_cSeq_eq_gammaSeq_mul_abs (ha : ¬IsSquare (-a : ℚ)) :
    ∀ d ≥ 1, |cSeq a d| = gammaSeq (normPoly a) a.sign d * |a| := by
  have ha0 := ne_zero_of_not_isSquare_neg a ha
  have hγ1 : gammaSeq (normPoly a) a.sign 1 = 1 := by
    rw [gammaSeq_one, eval_normPoly]
    rcases sign_eq_one_or_neg_one a ha0 with h | h <;> rw [h] <;> norm_num
  intro d hd
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · obtain rfl : d = 1 := by lia
    rw [hγ1, cSeq_one, abs_neg, one_mul]
  · rw [abs_of_pos (cSeq_pos a ha hd2)]
    exact (gammaSeq_mul_abs_eq_cSeq a (Int.sign_mul_abs a) hγ1 hd2).symm

lemma gammaSeq_normPoly_pos (ha : ¬IsSquare (-a : ℚ)) :
    ∀ d ≥ 1, 0 < gammaSeq (normPoly a) a.sign d := by
  have habs_pos : 0 < |a| := abs_pos.mpr (ne_zero_of_not_isSquare_neg a ha)
  intro d hd
  have hcabs_pos : 0 < |cSeq a d| := by
    rcases eq_or_lt_of_le hd with h1 | h2
    · rw [← h1]
      simpa using habs_pos
    · exact abs_pos.mpr (cSeq_pos a ha h2).ne'
  exact (mul_pos_iff_of_pos_right habs_pos).mp
    (abs_cSeq_eq_gammaSeq_mul_abs a ha d hd ▸ hcabs_pos)

lemma abs_bSeq_eq_betaSeq (ha : ¬IsSquare (-a : ℚ)) :
    ∀ n ≥ 2, |bSeq a n| = betaSeq (normPoly a) a.sign n := by
  have ha0 := ne_zero_of_not_isSquare_neg a ha
  have haQ : ((|a| : ℤ) : ℚ) ≠ 0 := by simpa using abs_ne_zero.mpr ha0
  intro n hn
  have hQ : ((|bSeq a n| : ℤ) : ℚ) = ((betaSeq (normPoly a) a.sign n : ℤ) : ℚ) := by
    rw [Int.cast_abs, intCast_bSeq a ha (by lia),
      intCast_betaSeq (evenPoly_normPoly a) (sign_eq_one_or_neg_one a ha0)
        (fun d hd ↦ (gammaSeq_normPoly_pos a ha d hd).ne') n (by lia),
      moebiusFactor_eq_prod, moebiusFactor_eq_prod, Finset.abs_prod]
    have hfac : ∀ x ∈ n.divisorsAntidiagonal,
        |(cSeq a x.2 : ℚ) ^ (μ x.1)|
          = ((gammaSeq (normPoly a) a.sign x.2 : ℤ) : ℚ) ^ (μ x.1)
            * ((|a| : ℤ) : ℚ) ^ (μ x.1) := by
      intro x hx
      have hx2 : 1 ≤ x.2 := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)
      rw [abs_zpow, ← Int.cast_abs, abs_cSeq_eq_gammaSeq_mul_abs a ha x.2 hx2]
      push_cast
      exact mul_zpow ..
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum haQ,
      moebius_antidiag_sum_zero n hn]
    simp
  exact_mod_cast hQ

/-- Section 3, main result: if `a > 0` and `a ≡ 1 or 2 mod 4`, or `a < 0`, `a ≡ 0 mod 4` and `-a` is
not a square, then `Gal(f_n/ℚ) ≅ [C_2]^n` for all `n ≥ 1`. -/
theorem section3_main
    (hcase : (0 < a ∧ a % 4 = 1) ∨ (0 < a ∧ a % 4 = 2) ∨ (a < 0 ∧ a % 4 = 0 ∧ ¬IsSquare (-a))) :
    ∀ n ≥ 1, Nonempty (GaloisGroup a n ≃* WreathPower n) := by
  intro n hn
  have ha : ¬IsSquare (-a : ℚ) := by
    obtain hpos | hnsq : 0 < a ∨ ¬IsSquare (-a) := by grind
    · exact not_isSquare_of_neg (mod_cast neg_neg_of_pos hpos)
    · exact fun hsq ↦ hnsq (Rat.isSquare_intCast_iff.mp (by push_cast; exact hsq))
  have ha0 := ne_zero_of_not_isSquare_neg a ha
  refine section1_squarefree a ha n fun k hk2 _ ↦ ?_
  rw [abs_bSeq_eq_betaSeq a ha k hk2]
  rw [← Rat.isSquare_intCast_iff]
  refine not_isSquare_betaSeq_of_pos (evenPoly_normPoly a) (sign_eq_one_or_neg_one a ha0)
    (gammaSeq_normPoly_pos a ha) ?_ k hk2
  have hg0 : (normPoly a).eval 0 = a.sign := by simp
  have hg1 : (normPoly a).eval 1 = |a| + a.sign := by simp
  rcases hcase with ⟨hpos, hmod⟩ | ⟨hpos, hmod⟩ | ⟨hneg, hmod, -⟩
  · exact .inl ⟨by rw [hg0, Int.sign_eq_one_of_pos hpos],
      by rw [hg1, abs_of_pos hpos, Int.sign_eq_one_of_pos hpos]; lia⟩
  · exact .inr ⟨.inl (by rw [hg0, Int.sign_eq_one_of_pos hpos]),
      by rw [hg1, abs_of_pos hpos, Int.sign_eq_one_of_pos hpos]; lia⟩
  · exact .inr ⟨.inr (by rw [hg0, Int.sign_eq_neg_one_of_neg hneg]),
      by rw [hg1, abs_of_neg hneg, Int.sign_eq_neg_one_of_neg hneg]; lia⟩

end

end QuadraticIterates
