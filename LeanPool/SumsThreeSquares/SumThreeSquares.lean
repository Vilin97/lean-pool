/-
Copyright (c) 2026 Bhavik Mehta, Pietro Monticone, Abel Doñate Muñoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Pietro Monticone, Abel Doñate Muñoz
-/
import LeanPool.SumsThreeSquares.MinkowskiConvex
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.Int.Basic

/-!
# Sums of three squares: the case `m ≡ 3 (mod 8)`

This file formalises the `m ≡ 3 (mod 8)` case of the three-squares theorem of
N. C. Ankeny: every positive integer not of the form `4ᵃ(8n + 7)` is a sum of
three squares. The proof follows Davenport's geometry-of-numbers argument via
Minkowski's theorem (see `LeanPool.SumsThreeSquares.MinkowskiConvex`).

The main result is `blueprint_case_mod8_eq3`.
-/

namespace LeanPool.SumsThreeSquares

open scoped BigOperators
open scoped Real Int
open scoped Nat
open scoped Pointwise

/-- A number is the sum of three squares. -/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n


/-- A prime `q ≡ 1 (mod 4)` with `(-2q / p) = 1` for every prime factor of `m`. -/
lemma exists_prime_aux (m : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧
      ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1 := by
  have hm_ne : m ≠ 0 := hm_sq.ne_zero
  -- For each prime `p ∣ m`, pick `a_p ≡ 1 (mod 4)`, `p ∤ a_p`, `(-2 a_p / p) = 1`.
  have ha_p : ∀ p : ℕ, p ∣ m → Nat.Prime p →
      ∃ a_p : ℕ, jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 ∧ a_p % 4 = 1 := by
    intro p hp hp_prime
    have hp_ne_two : p ≠ 2 := by
      rintro rfl
      exact absurd hp (by omega)
    obtain ⟨a_p, ha_p₁, ha_p₂⟩ :
        ∃ a_p : ℕ, jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 := by
      -- `p` is odd, so `-2` is a unit modulo `p`; transport a quadratic residue.
      obtain ⟨x, hx₁, hx₂⟩ : ∃ x : ℕ, jacobiSym x p = 1 ∧ x % p ≠ 0 :=
        ⟨1, by norm_num [jacobiSym], by norm_num [Nat.mod_eq_of_lt hp_prime.two_le]⟩
      obtain ⟨a_p, ha_p⟩ : ∃ a_p : ℕ, -2 * a_p ≡ x [ZMOD p] := by
        obtain ⟨y, hy⟩ : ∃ y : ℤ, -2 * y ≡ 1 [ZMOD p] := by
          have hgcd : Int.gcd (-2 : ℤ) p = 1 := by
            refine Nat.coprime_comm.mp (hp_prime.coprime_iff_not_dvd.mpr fun h => hp_ne_two ?_)
            have := Nat.le_of_dvd (by decide) h
            interval_cases p <;> trivial
          norm_num +zetaDelta at hgcd
          have := Int.gcd_eq_gcd_ab 2 (p : ℤ)
          exact ⟨-Int.gcdA 2 p, Int.modEq_iff_dvd.mpr ⟨Int.gcdB 2 p, by linarith⟩⟩
        refine ⟨Int.toNat (y * x % p), ?_⟩
        rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (Nat.cast_ne_zero.mpr hp_prime.ne_zero))]
        simpa [← ZMod.intCast_eq_intCast_iff, mul_assoc] using hy.mul_right x
      refine ⟨a_p, ?_, ?_⟩
      · rw [jacobiSym.mod_left] at hx₁ ⊢
        rw [ha_p]
        simpa [jacobiSym.mod_left] using hx₁
      · intro h
        haveI := Fact.mk hp_prime
        simp_all +decide [← ZMod.intCast_eq_intCast_iff]
        simp_all +decide [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
    -- Translate `a_p` modulo `p` so that also `a_p ≡ 1 (mod 4)`.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (a_p + k * p) % 4 = 1 := by
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
        have := hp_prime.eq_two_or_odd; omega
      obtain ⟨j, hj⟩ : ∃ j, p % 4 + 4 * j = p := ⟨p / 4, by omega⟩
      rcases hp4 with hp4 | hp4 <;> rw [hp4] at hj <;> rw [← hj]
      · exact ⟨(1 + 3 * a_p) % 4, by ring_nf; omega⟩
      · exact ⟨(3 + a_p) % 4, by ring_nf; omega⟩
    refine ⟨a_p + k * p, ?_, ?_, hk⟩
    · -- `(-2 (a_p + kp) / p) = (-2 a_p / p) = 1`.
      rw [Nat.cast_add, Nat.cast_mul, jacobiSym.mod_left,
        show -2 * ((a_p : ℤ) + (k : ℤ) * (p : ℤ)) =
            -2 * (a_p : ℤ) + (-(2 * (k : ℤ))) * (p : ℤ) from by ring,
        Int.add_mul_emod_self_right, ← jacobiSym.mod_left]
      exact ha_p₁
    · rw [Nat.add_mul_mod_self_right]; exact ha_p₂
  -- Combine the `a_p` via the Chinese Remainder Theorem into a single `a`.
  choose! a ha using ha_p
  obtain ⟨a_crt, ha_crt₁, ha_crt₂⟩ :
      ∃ a_crt : ℕ,
        (∀ p : ℕ, p ∣ m → Nat.Prime p → a_crt ≡ a p [MOD p]) ∧
        a_crt % 4 = 1 := by
    have h_crt_exists : ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p ∧ p ∣ m) →
        ∃ a_crt : ℕ, (∀ p ∈ S, a_crt ≡ a p [MOD p]) ∧ a_crt ≡ 1 [MOD 4] := by
      intro S
      induction S using Finset.induction with
      | empty => exact fun _ => ⟨1, by simp, Nat.ModEq.refl 1⟩
      | @insert p S hpS ih =>
        intro hS
        obtain ⟨a_crt, ha_crt₁, ha_crt₂⟩ := ih fun q hq =>
          hS q (Finset.mem_insert_of_mem hq)
        obtain ⟨x, hx⟩ :
            ∃ x : ℕ, x ≡ a_crt [MOD 4 * Finset.prod S id] ∧
              x ≡ a p [MOD p] := by
          have hcop : Nat.gcd (4 * Finset.prod S id) p = 1 := by
            refine Nat.Coprime.mul_left ?_ ?_
            · obtain ⟨_, hp_dvd⟩ := hS p (Finset.mem_insert_self _ _)
              refine Nat.Coprime.pow_left 2 (Nat.prime_two.coprime_iff_not_dvd.mpr fun h => ?_)
              have := Nat.mod_eq_zero_of_dvd h
              have := Nat.mod_eq_zero_of_dvd (dvd_trans h hp_dvd)
              omega
            · refine Nat.Coprime.prod_left fun q hq => Nat.coprime_comm.mp <|
                (hS p (Finset.mem_insert_self _ _)).1.coprime_iff_not_dvd.mpr fun h => hpS ?_
              have := Nat.prime_dvd_prime_iff_eq (hS p (Finset.mem_insert_self _ _)).1
                (hS q (Finset.mem_insert_of_mem hq)).1
              aesop
          exact ⟨_, (Nat.chineseRemainder hcop a_crt (a p)).2⟩
        refine ⟨x, fun q hq => ?_, (hx.1.of_dvd (dvd_mul_right 4 _)).trans ha_crt₂⟩
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hx.2
        · exact (hx.1.of_dvd (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) 4)).trans
            (ha_crt₁ q hq)
    obtain ⟨a_crt, h₁, h₂⟩ :=
      h_crt_exists (Nat.primeFactors m) fun p hp =>
        ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩
    refine ⟨a_crt, fun p hp hp_prime =>
      h₁ p (Nat.mem_primeFactors.mpr ⟨hp_prime, hp, hm_ne⟩), ?_⟩
    simpa [Nat.ModEq] using h₂
  -- `a_crt` is coprime to `4 * m`, so by Dirichlet there is a prime `q ≡ a_crt (mod 4m)`.
  have ha_crt_cop : Nat.Coprime a_crt (4 * m) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (show a_crt ≡ 1 [MOD 4] from ha_crt₂).gcd_eq.trans (by decide)
    · refine Nat.coprime_of_dvd' fun k hk hk₁ hk₂ => ?_
      exfalso
      have h1 : a_crt % k = 0 := Nat.mod_eq_zero_of_dvd hk₁
      have h2 : a_crt % k = a k % k := ha_crt₁ k hk₂ hk
      exact (ha k hk₂ hk).2.1 (by omega)
  obtain ⟨q, _, hq_prime, hq_modEq⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 0 (q := 4 * m) (a := a_crt) (by omega) ha_crt_cop
  refine ⟨q, hq_prime, ?_, fun p hp hp' => ?_⟩
  · -- `q % 4 = 1`.
    have hq4 : q % 4 = a_crt % 4 := hq_modEq.of_dvd (dvd_mul_right 4 m)
    omega
  · -- `(-2q / p) = (-2 a_crt / p) = (-2 (a p) / p) = 1`.
    have hqa : (q : ℤ) ≡ a_crt [ZMOD p] :=
      Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hp 4))
        (Int.natCast_modEq_iff.mpr hq_modEq)
    have hac : (a_crt : ℤ) ≡ a p [ZMOD p] :=
      Int.natCast_modEq_iff.mpr (ha_crt₁ p hp hp')
    rw [jacobiSym.mod_left, Int.ModEq.mul_left _ (hqa.trans hac), ← jacobiSym.mod_left]
    exact (ha p hp hp').1

/-
If $m \equiv 3 \pmod 8$ is squarefree, $q \equiv 1 \pmod 4$ is prime, and
$(-2q/p) = 1$ for all $p|m$, then $(-m/q) = 1$.
-/
lemma exists_odd_sq_mod_prime_of_jacobi_eq_one (m q : ℕ) (hq_prime : Nat.Prime q)
    (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b : ℤ, b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b % 2 = 1 := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℤ, b₀ ^ 2 ≡ -(m : ℤ) [ZMOD q] := by
    haveI := Fact.mk hq_prime
    norm_num [← ZMod.intCast_eq_intCast_iff, jacobiSym] at *
    norm_num [Nat.primeFactorsList_prime hq_prime] at h_jacobi
    rw [legendreSym.eq_one_iff] at h_jacobi
    · obtain ⟨x, hx⟩ := h_jacobi
      exact ⟨x.val, by simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm⟩
    · rw [legendreSym] at h_jacobi
      aesop
  by_cases hb₀_odd : b₀ % 2 = 1
  · exact ⟨b₀, hb₀, hb₀_odd⟩
  · refine ⟨b₀ + q, ?_, ?_⟩ <;>
      simp_all +decide [Int.ModEq, ← even_iff_two_dvd, parity_simps]
    · simp +decide [← hb₀, ← ZMod.intCast_eq_intCast_iff']
    · norm_num [Int.add_emod, Int.even_iff.mp hb₀_odd,
        show (q : ℤ) % 2 = 1 from mod_cast hq_prime.eq_two_or_odd.resolve_left (by aesop_cat)]

lemma jacobi_neg_m_q (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_mod : q % 4 = 1)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    jacobiSym (-m) q = 1 := by
  -- We need to show that $(q/m) = (-2/m)$.
  have h_jacobi_qm : jacobiSym q m = jacobiSym (-2) m := by
    have h_jacobi_qm : jacobiSym (-2 * q) m = 1 := by
      rw [jacobiSym];
      rw [List.prod_eq_one];
      intro x a
      simp_all only [Int.reduceNeg, neg_mul, List.mem_pmap, Nat.mem_primeFactorsList', ne_eq]
      obtain ⟨w, h⟩ := a
      obtain ⟨w_1, h⟩ := h
      obtain ⟨left, right⟩ := w_1
      obtain ⟨left_1, right⟩ := right
      subst h
      haveI := Fact.mk left; simp_all +decide [jacobiSym];
      specialize h_jacobi w left_1 left; simp_all +decide [Nat.primeFactorsList_prime left];
    rw [jacobiSym.mul_left] at h_jacobi_qm;
    rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at h_jacobi_qm; aesop;
  -- Since $(-m/q) = (q/m)$ and $(q/m) = (-2/m)$, we have $(-m/q) = (-2/m)$.
  have h_jacobi_neg_mq : jacobiSym (-m) q = jacobiSym q m := by
    rw [jacobiSym.neg _ (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_one_mod_four hq_mod, one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hq_mod
  rw [h_jacobi_neg_mq, h_jacobi_qm, jacobiSym.mod_right]
  · norm_num only [Int.natAbs]
    rw [hm_mod]
    norm_num [jacobiSym]
  · exact Nat.odd_iff.mpr (by omega)

/-
There exist integers $b$ and $h$ such that $b$ is odd and $b^2 - 4qh = -m$.
-/
lemma exists_b_h (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3)
    (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b h : ℤ, b % 2 = 1 ∧ b^2 - 4 * q * h = -m := by
  -- Since $(-m/q) = 1$, there is an integer `b` with `b^2 ≡ -m [ZMOD q]`.
  obtain ⟨b, hb_mod_q, hb_odd⟩ :=
    exists_odd_sq_mod_prime_of_jacobi_eq_one m q hq_prime hq_mod h_jacobi
  -- We need $b^2 \equiv -m \pmod{4q}$.
  have hb_mod : b ^ 2 ≡ -↑m [ZMOD (4 * ↑q : ℤ)] := by
    -- Since `q` is odd, combine the congruences modulo `q` and modulo `4`.
    have h_crt : b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b ^ 2 ≡ -↑m [ZMOD 4] := by
      exact ⟨hb_mod_q, by
        rw [← Int.emod_add_mul_ediv b 2, hb_odd]
        ring_nf
        norm_num [Int.ModEq, Int.add_emod, Int.sub_emod, Int.mul_emod]
        omega⟩
    rw [← Int.modEq_and_modEq_iff_modEq_mul]
    · exact h_crt.symm
    · exact Nat.Coprime.symm (hq_prime.coprime_iff_not_dvd.mpr fun h => by
        have := Nat.le_of_dvd (by decide) h
        interval_cases q <;> trivial)
  exact ⟨b, (b ^ 2 - (-m)) / (4 * q), hb_odd, by
    linarith [Int.ediv_mul_cancel
      (show (4 * q : ℤ) ∣ b ^ 2 - (-m) from hb_mod.symm.dvd)]⟩

/-
There exists an integer $t$ such that $2q t^2 \equiv -1 \pmod m$.
-/
lemma exists_t (m : ℕ) (q : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3)
    (hq_prime : Nat.Prime q)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, (2 * q : ℤ) * t ^ 2 ≡ -1 [ZMOD m] := by
  obtain ⟨t, ht⟩ :
      ∃ t : ℤ, ∀ p ∈ Nat.primeFactors m, 2 * q * t ^ 2 ≡ -1 [ZMOD p] := by
    have h_exists_tp (p : ℕ) (hp : p ∈ Nat.primeFactors m) :
        ∃ t_p : ℤ, 2 * q * t_p ^ 2 ≡ -1 [ZMOD p] := by
      obtain ⟨t, ht⟩ : ∃ t : ℤ, t ^ 2 ≡ -2 * q [ZMOD p] := by
        haveI := Fact.mk (Nat.prime_of_mem_primeFactors hp)
        simp_all +decide only [jacobiSym, Int.reduceNeg, neg_mul, Nat.mem_primeFactors,
          ne_eq, ← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_neg,
          Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        specialize h_jacobi p hp.2.1 hp.1
        simp_all +decide only [Nat.primeFactorsList_prime hp.1, List.pmap_cons, List.pmap_nil,
          List.prod_cons, List.prod_nil, mul_one]
        rw [legendreSym.eq_one_iff] at h_jacobi
        · obtain ⟨x, hx⟩ := h_jacobi
          use x.val
          simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
        · rw [legendreSym] at h_jacobi
          aesop
      obtain ⟨inv_2q, hinv_2q⟩ : ∃ inv_2q : ℤ, 2 * q * inv_2q ≡ 1 [ZMOD p] := by
        have h_inv : Int.gcd (2 * q : ℤ) p = 1 := by
          refine Nat.Coprime.mul_left ?_ ?_
          · simp_all only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq,
              Int.natAbs_natCast, Nat.coprime_two_left]
            obtain ⟨left, right⟩ := hp
            obtain ⟨left_1, right⟩ := right
            apply Odd.of_dvd_nat _ left_1
            rw [Nat.odd_iff]
            omega
          · rw [Nat.coprime_primes] <;>
            simp_all only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq, Int.natAbs_natCast]
            obtain ⟨left, right⟩ := hp
            obtain ⟨left_1, right⟩ := right
            apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only
            have := h_jacobi q left_1 left
            rw [jacobiSym.mod_left] at this
            norm_num at this
            rw [jacobiSym.zero_left] at this
            · aesop
            · exact left.one_lt
        exact Int.mod_coprime h_inv
      use t * inv_2q
      convert ht.mul_left (2 * q * inv_2q ^ 2) |> Int.ModEq.trans <| ?_ using 1 <;>
        ring_nf
      convert hinv_2q.pow 2 |> Int.ModEq.neg using 1
      ring
    choose! t ht using h_exists_tp
    have h_crt :
        ∀ p ∈ m.primeFactors,
          ∃ x : ℤ, x ≡ t p [ZMOD p] ∧
            ∀ q ∈ m.primeFactors, q ≠ p → x ≡ 0 [ZMOD q] := by
      intros p hp
      obtain ⟨y_p, hy_p⟩ :
          ∃ y_p : ℤ, y_p * (∏ q ∈ m.primeFactors \ {p}, (q : ℤ)) ≡
            1 [ZMOD p] := by
        have h_coprime : Nat.gcd p (∏ q ∈ m.primeFactors \ {p}, q) = 1 := by
          exact Nat.Coprime.prod_right fun q hq => by
            have := Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
              (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq |>.1))
            aesop
        have := Nat.gcd_eq_gcd_ab p (∏ q ∈ m.primeFactors \ { p }, q)
        simp_all only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq, and_imp,
          Nat.cast_one, Nat.cast_prod,
          not_false_eq_true, neg_add_rev, forall_const, implies_true]
        obtain ⟨left, right⟩ := hp
        obtain ⟨left_1, right⟩ := right
        exact ⟨Nat.gcdB p (∏ q ∈ m.primeFactors \ { p }, q), by
          rw [Int.modEq_iff_dvd]
          use Nat.gcdA p (∏ q ∈ m.primeFactors \ { p }, q)
          linarith⟩
      use y_p * (∏ q ∈ m.primeFactors \ {p}, (q : ℤ)) * t p
      exact ⟨by simpa using hy_p.mul_right _, fun q hq hqp =>
        Int.modEq_zero_iff_dvd.mpr <|
          dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ <| by aesop) _) _⟩
    choose! x hx₁ hx₂ using h_crt
    use ∑ p ∈ m.primeFactors, x p
    simp_all +decide only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq,
      ← ZMod.intCast_eq_intCast_iff, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_pow, Int.cast_neg, Int.cast_one, and_imp, not_false_eq_true, and_true,
      Int.cast_zero, Int.cast_sum]
    intro p pp dp dm
    rw [Finset.sum_eq_single p] <;> aesop
  -- Since $m$ is squarefree, $m = \prod p$, so $2q t^2 \equiv -1 \pmod m$.
  use t;
  -- Since $m$ is squarefree, it is the product of its distinct prime factors.
  have h_prod : (m : ℤ) = ∏ p ∈ Nat.primeFactors m, (p : ℤ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm_sq]
  simp_all +decide only [Int.reduceNeg, neg_mul, Nat.mem_primeFactors, ne_eq,
    Int.modEq_iff_dvd, and_imp]
  exact Finset.prod_dvd_of_coprime (fun p hp q hq hpq => by
    have := Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)
    aesop) fun p hp =>
      ht p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
        (by aesop_cat)

/-- The linear map `M` of the geometry-of-numbers argument. -/
noncomputable def linearMapM (m q : ℕ) (t b : ℤ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (![![2 * t * q, t * b, m],
      ![(Real.sqrt (2 * q)), b / (Real.sqrt (2 * q)), 0],
      ![0, Real.sqrt m / Real.sqrt (2 * q), 0]] : Matrix (Fin 3) (Fin 3) ℝ)

lemma det_linear_map_M (m q : ℕ) (t b : ℤ) (_hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linearMapM m q t b) = m * Real.sqrt m := by
  unfold linearMapM
  simp +decide only [Nat.ofNat_nonneg, Real.sqrt_mul, LinearMap.det_toLin',
    Matrix.det_fin_three, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val, mul_zero, zero_mul,
    sub_self, add_zero, zero_add, sub_zero]
  rw [mul_assoc, mul_div_cancel₀ _ (by positivity)]

lemma det_linear_map_M_ne_zero (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linearMapM m q t b) ≠ 0 := by
  rw [det_linear_map_M m q t b hm hq]
  positivity

/-- The linear map `M` reinterpreted on `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable abbrev linearMapMEuclidean (m q : ℕ) (t b : ℤ) :
    (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3)) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap ∘ₗ
    (linearMapM m q t b) ∘ₗ (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap

lemma det_linear_map_M_euclidean (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    LinearMap.det (linearMapMEuclidean m q t b) = m * Real.sqrt m := by
  have hrw : linearMapMEuclidean m q t b =
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv :
        (Fin 3 → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)).toLinearMap ∘ₗ
        (linearMapM m q t b) ∘ₗ
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv.symm).toLinearMap := rfl
  rw [hrw, LinearMap.det_conj]
  exact det_linear_map_M m q t b hm hq

/-
The volume of the preimage of the ball is $\frac{4}{3}\pi (2m)^{3/2} / m^{3/2}$.
-/
lemma vol_preimage_ball_euclidean (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    MeasureTheory.volume
        ((linearMapMEuclidean m q t b) ⁻¹'
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m)))) =
      ENNReal.ofReal
        ((4 / 3) * Real.pi * (2 * m) ^ (3 / 2 : ℝ) / (m * Real.sqrt m)) := by
  -- The volume of the preimage is $\text{vol}(B(0, \sqrt{2m})) / |\det M|$.
  have h_volume :
      (MeasureTheory.volume
          ((⇑(linearMapMEuclidean m q t b)) ⁻¹'
            (Metric.ball 0 (Real.sqrt (2 * ↑m))))) =
        (MeasureTheory.volume
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * ↑m)))) /
        ENNReal.ofReal (abs (LinearMap.det (linearMapMEuclidean m q t b))) := by
    have h_volume_image :
        ∀ {L : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3))},
          LinearMap.det L ≠ 0 →
          ∀ {E : Set (EuclideanSpace ℝ (Fin 3))}, MeasurableSet E →
            MeasureTheory.volume (L ⁻¹' E) =
              MeasureTheory.volume E / ENNReal.ofReal (abs (LinearMap.det L)) := by
      intro L hL E hE
      rw [div_eq_mul_inv]
      rw [MeasureTheory.Measure.addHaar_preimage_linearMap]
      · simp_all only [ne_eq, abs_inv, abs_pos, not_false_eq_true,
          ENNReal.ofReal_inv_of_pos]
        ring
      · assumption
    apply h_volume_image
    · rw [det_linear_map_M_euclidean m q t b hm hq]
      positivity
    · exact measurableSet_ball
  -- The volume of the ball of radius $\sqrt{2m}$ is $\frac{4}{3}\pi (\sqrt{2m})^3$.
  have h_ball_volume :
      (MeasureTheory.volume
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * ↑m)))) =
        ENNReal.ofReal ((4 / 3) * Real.pi * (Real.sqrt (2 * ↑m)) ^ 3) := by
    norm_num +zetaDelta at *
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
    ring_nf
    rw [← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  -- The determinant of the linear map is $m^{3/2}$.
  have h_det : abs (LinearMap.det (linearMapMEuclidean m q t b)) = m * Real.sqrt m := by
    convert congr_arg abs (det_linear_map_M_euclidean m q t b hm hq) using 1
    rw [abs_of_nonneg (by positivity)]
  rw [h_volume, h_ball_volume, h_det, ENNReal.ofReal_div_of_pos]
  · rw [show (Real.sqrt (2 * m)) ^ 3 = (2 * m) ^ (3 / 2 : ℝ) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num]
  · positivity

/-
The calculated volume is greater than 8.
-/
lemma volume_inequality : (4 / 3) * Real.pi * (2 : ℝ) ^ (3 / 2 : ℝ) > 8 := by
  rw [show (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add'] <;> norm_num]
  nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]

lemma quad_form_decomposition (m q : ℕ) (b h x y : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
      (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 =
      2 * ((q : ℝ) * x ^ 2 + (b : ℝ) * x * y + (h : ℝ) * y ^ 2) := by
  have hsqrt_2q_pos : (Real.sqrt 2 * Real.sqrt q : ℝ) ≠ 0 := by positivity
  have hsqrt_m_sq : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m)
  have hb2 : (b : ℝ) ^ 2 = 4 * q * h - m := by
    have h1 : (b : ℤ) ^ 2 = 4 * q * h - m := by linarith [hbqm]
    exact_mod_cast h1
  have hb2' : (b : ℝ) ^ 2 + m = 4 * q * h := by linarith [hb2]
  field_simp [hsqrt_2q_pos]
  rw [show (Real.sqrt 2 : ℝ) ^ 2 = 2 by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)],
    show (Real.sqrt q : ℝ) ^ 2 = q by
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (q : ℝ))],
    hsqrt_m_sq]
  ring_nf
  nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), hb2', hb2]


private lemma exists_lattice_xyz_lt_two_m (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    let R := (2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z
    let S := Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y
    let T := Real.sqrt m / Real.sqrt (2 * q) * y
    R^2 + S^2 + T^2 < 2 * m := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))
  let S_pre := (linearMapMEuclidean m q t b) ⁻¹' B
  have h_symm : ∀ x ∈ S_pre, -x ∈ S_pre := by
    intro x hx
    unfold S_pre B at hx ⊢
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hx ⊢
    rw [map_neg, norm_neg]
    exact hx
  have h_conv : Convex ℝ S_pre := by
    unfold S_pre
    apply Convex.linear_preimage
    exact convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))
  have h_vol : (2 : ENNReal) ^ 3 < MeasureTheory.volume S_pre := by
    unfold S_pre
    rw [vol_preimage_ball_euclidean m q t b hm hq]
    norm_num
    ring_nf
    field_simp
    ring_nf
    have : (m : ℝ) * √(m : ℝ) = (m : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_div_two_eq_sqrt, (by norm_num : (3  : ℝ) = 2 + 1), Real.rpow_add]
      · simp only [Real.rpow_ofNat, Nat.cast_nonneg, Real.sq_sqrt, Real.rpow_one]
      all_goals positivity
    rw [this, Real.mul_rpow, mul_comm π, mul_assoc, mul_assoc, mul_lt_mul_iff_right₀]
    · rw [← pow_lt_pow_iff_left₀ (n := 2)]
      · norm_num1
        rw [mul_pow, ← Real.rpow_two, ← Real.rpow_mul (by simp)]
        nlinarith [Real.pi_gt_d4]
      · simp
      · positivity
      · positivity
    all_goals positivity
  let E := EuclideanSpace ℝ (Fin 3)
  have := classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure h_symm h_conv h_vol
  obtain ⟨x, hx0, hxs, h⟩ := this
  have hcoor0 := h 0
  have hcoor1 := h 1
  have hcoor2 := h 2
  obtain ⟨R, hr⟩ := hcoor0
  obtain ⟨S, hs⟩ := hcoor1
  obtain ⟨T, ht⟩ := hcoor2
  use R, S, T
  constructor
  · contrapose! hx0
    ext i
    fin_cases i <;> aesop
  · convert (show (‖linearMapMEuclidean m q t b x‖ ^ 2 : ℝ) < 2 * m from ?_)
      using 1 <;> norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    all_goals ring_nf
    all_goals
      simp_all only [Nat.ofNat_nonneg, Real.sqrt_mul, Set.mem_preimage, Metric.mem_ball,
        dist_zero_right, map_neg, norm_neg, implies_true, ne_eq, Fin.isValue,
        Real.sq_sqrt, Nat.cast_nonneg, inv_pow, S_pre, B]
    · have h_expand :
          (linearMapMEuclidean m q t b x) 0 = 2 * t * q * x 0 + t * b * x 1 +
            m * x 2 ∧
        (linearMapMEuclidean m q t b x) 1 =
          Real.sqrt (2 * q) * x 0 + b / Real.sqrt (2 * q) * x 1 ∧
        (linearMapMEuclidean m q t b x) 2 = Real.sqrt m / Real.sqrt (2 * q) * x 1 := by
        unfold linearMapMEuclidean
        norm_num [Fin.sum_univ_three]
        ring_nf
        erw [Matrix.toLin'_apply]
        ring_nf
        simp_all (config := { decide := true }) only [Fin.isValue]
        apply And.intro
        · norm_num [Matrix.mulVec]
          ring_nf!
        · apply And.intro
          · simp [Matrix.mulVec]
            ring!
          · simp (config := { decide := Bool.true }) [Matrix.mulVec]
            ring_nf
            aesop (simp_config := { decide := Bool.true })
      rw [Real.sq_sqrt <| by positivity]
      have heq : ∀ i, (linearMapM m q t b) ((EuclideanSpace.equiv (Fin 3) ℝ) x) i =
          ((linearMapMEuclidean m q t b) x).ofLp i := fun _ => rfl
      simp only [heq]
      rw [h_expand.1, h_expand.2.1, h_expand.2.2]
      ring_nf
      norm_num [ne_of_gt, hq, hm]
      ring_nf
      norm_num [hq.ne', hm.ne']
      ring
    · simp +zetaDelta only [LinearMap.coe_comp,
        ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_symm_toLinearEquiv,
        ContinuousLinearEquiv.coe_toLinearEquiv, Function.comp_apply,
        PiLp.continuousLinearEquiv_symm_apply, Fin.isValue] at *
      rw [EuclideanSpace.norm_eq] at hxs
      simp_all only [Fin.isValue, Real.norm_eq_abs, sq_abs]
      rw [Real.sq_sqrt <| by positivity]
      rw [← Real.sqrt_mul <| by positivity] at *
      rw [Real.sqrt_lt_sqrt_iff <| by positivity] at *
      norm_num [Fin.sum_univ_three] at *
      linarith!

private lemma rst_expand_eq (m q : ℕ) (t b h x y z : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
      (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 =
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) := by
  have hqf :=
    congrArg
      (fun u : ℝ => (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 + u)
      (quad_form_decomposition m q b h x y hq hbqm)
  calc
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
        (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
        (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2
        = (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
            ((Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
              (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2) := by ring
    _ = (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
          2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) := by
          simpa [add_assoc, add_left_comm, add_comm] using hqf

private lemma rst_modEq_zero (m q : ℕ) (t b h x y z : ℤ)
    (hqt : t ^ 2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * q * h = -m) :
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) ≡ 0 [ZMOD m] := by
  have hsplit :
      (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
          2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) =
        (t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2) +
        (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m := by ring
  rw [hsplit]
  have hdrop :
      (t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2) +
        (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m
      ≡ t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 [ZMOD m] := by
    have h0 : (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m ≡ 0 [ZMOD m] :=
      Int.modEq_zero_iff_dvd.mpr ⟨t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2, by ring⟩
    simpa only [add_zero] using (Int.ModEq.refl _).add h0
  have hqt_xy : (t ^ 2 * 2 * ↑q) * (x * b * y * 2) ≡ (-1) * (x * b * y * 2) [ZMOD m] := by
    simpa using hqt.mul_right (x * b * y * 2)
  have hqt_x2 : (t ^ 2 * 2 * ↑q) * (↑q * x ^ 2 * 2) ≡ (-1) * (↑q * x ^ 2 * 2) [ZMOD m] := by
    simpa using hqt.mul_right (↑q * x ^ 2 * 2)
  have hreplace :
      (t ^ 2 * 2 * ↑q) * (x * b * y * 2) +
          (t ^ 2 * 2 * ↑q) * (↑q * x ^ 2 * 2) + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2
      ≡ (-1) * (x * b * y * 2) + (-1) * (↑q * x ^ 2 * 2) + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 [ZMOD m] := by
    apply Int.ModEq.add
    · apply Int.ModEq.add
      · apply Int.ModEq.add
        · apply Int.ModEq.add
          · apply Int.ModEq.add
            · exact hqt_xy
            · exact hqt_x2
          · exact Int.ModEq.refl _
        · exact Int.ModEq.refl _
      · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hb2 : (b : ℤ) ^ 2 = 4 * q * h - m := by linarith [hbqm]
  have ht2b2 : t ^ 2 * b ^ 2 ≡ t ^ 2 * (4 * q * h) [ZMOD m] := by
    calc
      t ^ 2 * b ^ 2 = t ^ 2 * (4 * q * h - m) := by rw [hb2]
      _ = t ^ 2 * (4 * q * h) - t ^ 2 * m := by ring
      _ ≡ t ^ 2 * (4 * q * h) - 0 [ZMOD m] := by
            apply Int.ModEq.sub (Int.ModEq.refl _)
            exact Int.modEq_zero_iff_dvd.mpr ⟨t ^ 2, by ring⟩
      _ = t ^ 2 * (4 * q * h) := by ring
  have ht2_4qh : t ^ 2 * (4 * q * h) ≡ -2 * h [ZMOD m] := by
    calc
      t ^ 2 * (4 * q * h) = (t ^ 2 * 2 * q) * (2 * h) := by ring
      _ ≡ (-1) * (2 * h) [ZMOD m] := hqt.mul_right _
      _ = -2 * h := by ring
  calc
    (t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2) +
        (t * q * x * z * 4 + t * b * y * z * 2 + m * z ^ 2) * m
      ≡ t ^ 2 * ↑q * x * b * y * 4 + t ^ 2 * ↑q ^ 2 * x ^ 2 * 4 + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 [ZMOD m] := hdrop
    _ = (t ^ 2 * 2 * ↑q) * (x * b * y * 2) +
        (t ^ 2 * 2 * ↑q) * (↑q * x ^ 2 * 2) + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 := by ring
    _ ≡ (-1) * (x * b * y * 2) + (-1) * (↑q * x ^ 2 * 2) + t ^ 2 * b ^ 2 * y ^ 2 +
          ↑q * x ^ 2 * 2 + x * b * y * 2 + y ^ 2 * h * 2 [ZMOD m] := hreplace
    _ = t ^ 2 * b ^ 2 * y ^ 2 + y ^ 2 * h * 2 := by ring
    _ ≡ (t ^ 2 * (4 * q * h)) * y ^ 2 + y ^ 2 * h * 2 [ZMOD m] := by
      apply Int.ModEq.add _ (Int.ModEq.refl _)
      exact ht2b2.mul_right _
    _ ≡ (-2 * h) * y ^ 2 + y ^ 2 * h * 2 [ZMOD m] := by
      apply Int.ModEq.add _ (Int.ModEq.refl _)
      exact ht2_4qh.mul_right _
    _ = 0 := by ring

private lemma xyz_zero_of_sum_sq_eq_zero (m q : ℕ) (t b x y z : ℤ)
    (hm : 0 < m) (hq : 0 < q)
    (hsum0 :
      (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
        (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
        (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hT0sq : (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ),
      sq_nonneg
        (Real.sqrt 2 * Real.sqrt q * x +
          (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y),
      hsum0]
  have hT0 : (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y : ℝ) = 0 := by
    nlinarith [hT0sq]
  have hy0R : (y : ℝ) = 0 := by
    have hcoef : (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hT0).resolve_left hcoef
  have hy0 : y = 0 := by exact_mod_cast hy0R
  have hS0sq :
      (Real.sqrt 2 * Real.sqrt q * x +
        (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ),
      sq_nonneg (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y), hsum0]
  have hS0 :
      (Real.sqrt 2 * Real.sqrt q * x +
        (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y : ℝ) = 0 := by
    nlinarith [hS0sq]
  have hx0R : (x : ℝ) = 0 := by
    have hcoef : (Real.sqrt 2 * Real.sqrt q : ℝ) ≠ 0 := by positivity
    have hlin : (Real.sqrt 2 * Real.sqrt q : ℝ) * x = 0 := by
      simpa [hy0R] using hS0
    exact (mul_eq_zero.mp hlin).resolve_left hcoef
  have hx0 : x = 0 := by exact_mod_cast hx0R
  have hR0sq : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 = 0 := by
    nlinarith [
      sq_nonneg
        (Real.sqrt 2 * Real.sqrt q * x +
          (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y),
      sq_nonneg (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y), hsum0]
  have hR0 : (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) = 0 := by
    nlinarith [hR0sq]
  have hz0R : (z : ℝ) = 0 := by
    have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hlin : (m : ℝ) * z = 0 := by
      simpa [hx0R, hy0R] using hR0
    exact (mul_eq_zero.mp hlin).resolve_left hmne
  have hz0 : z = 0 := by exact_mod_cast hz0R
  exact ⟨hx0, hy0, hz0⟩



lemma exists_Rv_from_Minkowski (m q : ℕ) (t b h : ℤ) (hm : 0 < m) (hq : 0 < q)
    (hqt : t ^ 2 * 2 * q ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    ∃ (x y : ℤ) (R : ℤ) (v : ℕ),
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  have h_exists : ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧
      (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
      (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
      (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 < 2 * m := by
    simpa using exists_lattice_xyz_lt_two_m m q t b hm hq
  obtain ⟨x, y, z, hne, hlt⟩ := h_exists;
  -- The integer expression is nonnegative, divisible by `m`, and strictly below `2m`.
  have h_cases :
      (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
          2 * (q * x ^ 2 + b * x * y + h * y ^ 2) = 0 ∨
        (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
          2 * (q * x ^ 2 + b * x * y + h * y ^ 2) = m := by
    have h_cases :
        (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
            2 * (q * x ^ 2 + b * x * y + h * y ^ 2) ≡ 0 [ZMOD m] := by
      exact rst_modEq_zero m q t b h x y z hqt hbqm
    have h_cases :
        (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
          2 * (q * x ^ 2 + b * x * y + h * y ^ 2) < 2 * m := by
      have h_expand : (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
          (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
          (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 =
          (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
          2 * (q * x ^ 2 + b * x * y + h * y ^ 2) := by
        calc
          (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
              (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
              (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2
              = (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
                (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
                (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (2 * t * q * x + t * b * y + m * z : ℝ) ^ 2 +
              2 * (q * x ^ 2 + b * x * y + h * y ^ 2) :=
                rst_expand_eq m q t b h x y z (by positivity) (by simpa using hbqm)
      exact_mod_cast h_expand ▸ hlt;
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp ‹_›;
    have hquad_nonneg : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (2 * q * x + b * y)]
    have hexpr_nonneg : 0 ≤ (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
        2 * (q * x ^ 2 + b * x * y + h * y ^ 2) := by
      nlinarith [sq_nonneg (2 * t * q * x + t * b * y + m * z), hquad_nonneg]
    have hk_nonneg : 0 ≤ k := by
      have hm_nonneg : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
      nlinarith [hk, hexpr_nonneg, hm_nonneg]
    have hk_lt_two : k < 2 := by
      have hm_pos' : (0 : ℤ) < m := by exact_mod_cast hm
      nlinarith [hk, h_cases, hm_pos']
    have hk_zero_or_one : k = 0 ∨ k = 1 := by omega
    rcases hk_zero_or_one with rfl | rfl
    · left
      nlinarith [hk]
    · right
      nlinarith [hk]
  rcases h_cases with h_case1 | h_case2
  · -- If $R^2 + 2v = 0$, then `x = y = z = 0`.
    have h_contra : x = 0 ∧ y = 0 ∧ z = 0 := by
      apply xyz_zero_of_sum_sq_eq_zero m q t b x y z hm hq
      have hsum0 :
          (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
            (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
            (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 = 0 := by
        calc
          (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
              (Real.sqrt 2 * Real.sqrt q * x + (b : ℝ) / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2 +
              (Real.sqrt m / (Real.sqrt 2 * Real.sqrt q) * y) ^ 2
              = (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z : ℝ) ^ 2 +
                2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) :=
                  rst_expand_eq m q t b h x y z hq (by simpa using hbqm)
          _ = 0 := by
                simpa using congr_arg ((↑) : ℤ → ℝ) h_case1
      exact hsum0
    aesop
  · refine ⟨x, y, 2 * t * q * x + t * b * y + m * z,
      Int.toNat (q * x ^ 2 + b * x * y + h * y ^ 2), ?_, ?_, ?_⟩ <;> norm_num
    · nlinarith [sq_nonneg (2 * q * x + b * y)]
    · rw [max_eq_left]
      · convert h_case2 using 1
      · nlinarith [sq_nonneg (2 * q * x + b * y)]
    · contrapose! hne
      have hxy_zero : x = 0 ∧ y = 0 := by
        have hxy_zero : q * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
          nlinarith [sq_nonneg (2 * q * x + b * y)]
        by_cases hy : y = 0
        · aesop
        · nlinarith [sq_nonneg (2 * q * x + b * y), mul_self_pos.mpr hy]
      simp_all +decide only [Int.reduceNeg, Int.cast_zero, mul_zero, add_zero, zero_add,
        Nat.ofNat_nonneg, Real.sqrt_mul, ne_eq, zero_pow, Std.le_refl, Prod.mk.injEq,
        true_and]
      rcases m with (_ | _ | m) <;> norm_num at *
      · exact absurd (congr_arg (· % 4) hbqm) (by
          norm_num [sq, Int.add_emod, Int.sub_emod, Int.mul_emod]
          have := Int.emod_nonneg b four_pos.ne'
          have := Int.emod_lt_of_pos b four_pos
          interval_cases b % 4 <;> trivial)
      · nlinarith [show z ^ 2 * (m + 1 + 1) = 1 by nlinarith]
/-- There exist `q, b, h, t, x, y, z` yielding `R² + 2v = m` with `v > 0`. -/
lemma exists_R_v_of_mod8_eq3 (m : ℕ) (hm : Squarefree m) (hm_pos : 0 < m) (hmod : m % 8 = 3) :
    ∃ (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ),
      Nat.Prime q ∧ q % 4 = 1 ∧
      (∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) ∧
      b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ) ∧
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  obtain ⟨q, hq_prime, hq_mod, hjac⟩ := exists_prime_aux m hm hmod
  obtain ⟨b, h, _, hbqm⟩ :=
    exists_b_h m q hmod hq_prime hq_mod (jacobi_neg_m_q m q hmod hq_mod hjac)
  obtain ⟨t, hqt⟩ := exists_t m q hm hmod hq_prime hjac
  have hqt' : t ^ 2 * 2 * q ≡ -1 [ZMOD m] := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hqt
  obtain ⟨x, y, R, v, hv_def, hRv, hv_pos⟩ :=
    exists_Rv_from_Minkowski m q t b h hm_pos (hq_prime.pos) hqt' hbqm
  exact ⟨q, b, h, x, y, R, v, hq_prime, hq_mod, hjac, hbqm, hv_def, hRv, hv_pos⟩

lemma jacobi_neg_d_of_dvd_sq_add (p : ℕ) (a d b' : ℤ)
    (hp : Nat.Prime p) (_hp_odd : p ≠ 2)
    (hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (hp_not_dvd_b : ¬ (p : ℤ) ∣ b') :
    jacobiSym (-d) p = 1 := by
  haveI := Fact.mk hp
  rw [jacobiSym]
  norm_num [Nat.primeFactorsList_prime hp]
  simp_all +decide only [ne_eq, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add,
    Int.cast_pow, Int.cast_mul, Int.cast_neg, neg_eq_zero, not_false_eq_true,
    legendreSym.eq_one_iff]
  use a / b'
  grind

lemma jacobi_neg_d_of_odd_padicVal (p : ℕ) (a d b' : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (h_odd_val : ¬ Even (padicValInt p (a ^ 2 + d * b' ^ 2))) :
    jacobiSym (-d) p = 1 := by
  haveI := Fact.mk hp
  have hpp : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  -- Strong induction on `|a| + |b'|`.
  suffices H : ∀ n : ℕ, ∀ a b' : ℤ, a.natAbs + b'.natAbs = n →
      ¬ Even (padicValInt p (a ^ 2 + d * b' ^ 2)) → jacobiSym (-d) p = 1 from
    H _ a b' rfl h_odd_val
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b' hn hodd
    -- `p ∣ a^2 + d*b'^2`: otherwise its `p`-adic valuation is `0`, contradicting `hodd`.
    have hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2 := by
      by_contra h
      exact hodd (by rw [padicValInt.eq_zero_of_not_dvd h]; decide)
    by_cases h_div_b' : (p : ℤ) ∣ b'
    · -- Then `p ∣ a` too; descend to `(a / p, b' / p)`.
      obtain ⟨k, rfl⟩ := h_div_b'
      have hp_dvd_a2 : (p : ℤ) ∣ a ^ 2 := by
        have hd : (p : ℤ) ∣ d * (p * k) ^ 2 :=
          Dvd.dvd.mul_left (dvd_pow (dvd_mul_right _ _) two_ne_zero) d
        exact (dvd_add_right hd).mp (by rwa [add_comm] at hp_dvd)
      obtain ⟨a', rfl⟩ : ∃ a', a = p * a' := Int.Prime.dvd_pow' hp hp_dvd_a2
      have hfactor : (p * a') ^ 2 + d * (p * k) ^ 2 =
          (p : ℤ) * (p : ℤ) * (a' ^ 2 + d * k ^ 2) := by
        ring
      -- The new pair has nonzero quadratic-form value (else the valuation would be even).
      have hsum_ne : a' ^ 2 + d * k ^ 2 ≠ 0 := by
        rintro h0
        exact hodd (by rw [hfactor, h0, mul_zero, padicValInt.zero]; decide)
      -- Its valuation is still odd, since `padicValInt p (p²)` is even.
      have hodd' : ¬ Even (padicValInt p (a' ^ 2 + d * k ^ 2)) := by
        have hval : padicValInt p ((p * a') ^ 2 + d * (p * k) ^ 2)
            = 2 * padicValInt p p + padicValInt p (a' ^ 2 + d * k ^ 2) := by
          rw [hfactor, padicValInt.mul (mul_ne_zero hpp hpp) hsum_ne,
            padicValInt.mul hpp hpp]
          ring
        rw [hval, Nat.even_iff] at hodd
        rw [Nat.even_iff]
        omega
      -- The new pair is strictly smaller.
      have hab : ((p : ℤ) * a').natAbs = p * a'.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hkb : ((p : ℤ) * k).natAbs = p * k.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hlt : a'.natAbs + k.natAbs < n := by
        rw [← hn, hab, hkb, ← Nat.left_distrib]
        rcases Nat.eq_zero_or_pos (a'.natAbs + k.natAbs) with hz | hpos
        · obtain ⟨ha0, hk0⟩ := Nat.add_eq_zero_iff.mp hz
          rw [Int.natAbs_eq_zero] at ha0 hk0
          exact absurd (by rw [ha0, hk0]; ring) hsum_ne
        · exact lt_mul_of_one_lt_left hpos hp.one_lt
      exact ih _ hlt a' k rfl hodd'
    · exact jacobi_neg_d_of_dvd_sq_add p a d b' hp hp_odd hp_dvd hp_not_dvd_d h_div_b'

lemma p_mod4_eq1_of_dvd_v_not_dvd_m (p : ℕ) (q : ℤ) (b h x y v R m : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -m)
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : ¬ Even (padicValInt p v))
    (hpm : ¬ (p : ℤ) ∣ m) :
    p % 4 = 1 := by
  have h_jacobi_m : jacobiSym m p = 1 := by
    have hm_mod : (R ^ 2 : ℤ) ≡ m [ZMOD p] := by
      norm_num [← hRv, Int.modEq_iff_dvd]
      refine dvd_mul_of_dvd_right ?_ _
      contrapose! hpv
      simp_all +decide [padicValInt.eq_zero_of_not_dvd]
    haveI := Fact.mk hp
    simp_all +decide only [ne_eq, Nat.not_even_iff_odd, ← ZMod.intCast_eq_intCast_iff,
      Int.cast_pow, jacobiSym]
    simp +decide only [Nat.primeFactorsList_prime hp, List.pmap_cons, List.pmap_nil, List.prod_cons,
      List.prod_nil, mul_one]
    haveI := Fact.mk hp
    rw [legendreSym.eq_one_iff]
    · aesop
    · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpm
  have h_jacobi_neg_m : jacobiSym (-m) p = 1 := by
    by_cases hpq : (p : ℤ) ∣ q <;> simp_all only [ne_eq, Nat.not_even_iff_odd]
    · have hb_sq_mod_p : b ^ 2 ≡ -m [ZMOD p] := by
        exact Int.modEq_iff_dvd.mpr ⟨-4 * h * hpq.choose, by
          linear_combination -hbqm - 4 * h * hpq.choose_spec⟩
      haveI := Fact.mk hp
      simp_all +decide only [jacobiSym, ← ZMod.intCast_eq_intCast_iff, Int.cast_pow,
        Int.cast_neg]
      simp_all +decide only [Nat.primeFactorsList_prime hp, List.pmap_cons, List.pmap_nil,
        List.prod_cons, List.prod_nil, mul_one]
      rw [legendreSym.eq_one_iff] at *
      · exact ⟨b, by simpa [sq] using hb_sq_mod_p.symm⟩
      · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpm
      · simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    · have h_jacobi_neg_m_odd : ¬ Even (padicValInt p ((2 * q * x + b * y) ^ 2 + m * y ^ 2)) := by
        have h_jacobi_neg_m_odd : padicValInt p (4 * q * v) = padicValInt p v := by
          haveI := Fact.mk hp
          rw [padicValInt.mul, padicValInt.mul] <;> norm_num
          · exact ⟨Or.inr <| mod_cast fun h => hp_odd <| by
                have := Nat.le_of_dvd (by decide) h
                interval_cases p <;> trivial,
              Or.inr <| Or.inr hpq⟩
          · aesop
          · aesop_cat
          · aesop
        grind
      apply jacobi_neg_d_of_odd_padicVal p (2 * q * x + b * y) m y hp hp_odd hpm
        h_jacobi_neg_m_odd
  have h_jacobi_neg_1 : jacobiSym (-1) p = 1 := by
    have h_mul : jacobiSym (-m) p = jacobiSym (-1) p * jacobiSym m p := by
      simpa [neg_mul] using (jacobiSym.mul_left (-1) m p)
    rw [h_mul, h_jacobi_m] at h_jacobi_neg_m
    simpa using h_jacobi_neg_m
  rw [jacobiSym.at_neg_one] at h_jacobi_neg_1
  · rw [ZMod.χ₄_nat_mod_four] at h_jacobi_neg_1
    have := Nat.mod_lt p zero_lt_four
    interval_cases p % 4 <;> trivial
  · exact hp.odd_of_ne_two hp_odd

lemma p_mod4_of_dvd_v_dvd_m (p : ℕ) (q : ℕ) (b h x y : ℤ) (R v : ℤ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3)
    (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m)
    (hjac : jacobiSym (-2 * q) p = 1) :
    False := by
  have hp_R : (p : ℤ) ∣ R := by
    exact Int.Prime.dvd_pow' hp <| by
      rw [← Int.dvd_add_left (dvd_mul_of_dvd_right hpv _)]
      exact hRv.symm ▸ Int.natCast_dvd_natCast.mpr hpm
  have hp_2qx_by : (p : ℤ) ∣ (2 * q * x + b * y) := by
    have hp_2qx_by : (p : ℤ) ∣ ((2 * q * x + b * y) ^ 2 + m * y ^ 2) := by
      convert hpv.mul_left (4 * q) using 1
      rw [hv]
      linear_combination hbqm * y ^ 2
    haveI := Fact.mk hp
    simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨k, hk⟩ := hpm
    simp_all
  have h_y_sq_mod_p : y ^ 2 ≡ 2 * q [ZMOD p] := by
    have h_div_p : (m / p : ℤ) * y ^ 2 ≡ (m / p : ℤ) * (2 * q) [ZMOD p] := by
      have h_div_p : (4 * q * v : ℤ) ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
        obtain ⟨k, hk⟩ := hpv
        simp_all +decide only [Int.reduceNeg, neg_mul, Int.modEq_iff_dvd]
        obtain ⟨a, ha⟩ := hp_R
        obtain ⟨b', hb'⟩ := hp_2qx_by
        simp_all +decide only [← eq_sub_iff_add_eq', ← mul_assoc]
        exact ⟨a ^ 2 * 2 * q, by nlinarith⟩
      have h_div_p : (4 * q * v : ℤ) ≡ (2 * q * x + b * y) ^ 2 + m * y ^ 2 [ZMOD p ^ 2] := by
        exact Int.modEq_of_dvd ⟨0, by rw [hv]; linear_combination hbqm * y ^ 2⟩
      have h_div_p : (m : ℤ) * y ^ 2 ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
        simp_all +decide only [Int.reduceNeg, neg_mul, Int.ModEq]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at *
        aesop
      rw [Int.modEq_iff_dvd] at *
      obtain ⟨k, hk⟩ := h_div_p
      use k
      nlinarith [hp.two_le, Int.ediv_mul_cancel (show (p : ℤ) ∣ m from mod_cast hpm)]
    haveI := Fact.mk hp
    simp_all +decide [← ZMod.intCast_eq_intCast_iff]
    cases h_div_p <;> simp_all +decide [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_cast at *
    simp_all +decide [Nat.squarefree_iff_prime_squarefree]
  have h_jacobi_2q_p : jacobiSym (2 * q) p = 1 := by
    haveI := Fact.mk hp
    simp_all +decide only [jacobiSym, Int.reduceNeg, neg_mul,
      ← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast]
    simp_all +decide only [Nat.primeFactorsList_prime hp, List.pmap_cons, List.pmap_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [legendreSym.eq_one_iff]
    · exact ⟨y, by simpa [sq, ← ZMod.intCast_eq_intCast_iff] using h_y_sq_mod_p.symm⟩
    · intro H
      simp_all +decide [legendreSym]
  haveI := Fact.mk hp
  simp_all +decide only [Int.reduceNeg, neg_mul, ← ZMod.intCast_eq_intCast_iff,
    Int.cast_pow, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, jacobiSym.mul_left]
  rw [jacobiSym.neg] at hjac
  · rw [ZMod.χ₄_nat_mod_four] at hjac
    simp_all +decide [jacobiSym.mul_left]
  · exact hp.odd_of_ne_two <| by aesop_cat

lemma even_padicVal_of_mod4_eq3 (p : ℕ) (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3)
    (hm_sq : Squarefree m)
    (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p', p' ∣ m → Nat.Prime p' → jacobiSym (-2 * ↑q) ↑p' = 1) :
    Even (padicValNat p (2 * v)) := by
  by_cases hp2 : p = 2
  · aesop
  · by_cases hpv : (p : ℤ) ∣ v
    · by_cases hpm : (p : ℕ) ∣ m
      · have := p_mod4_of_dvd_v_dvd_m p q b h x y R v m hp hp3 hm_sq
          hv_def hbqm hRv hpv hpm (hjac p hpm hp)
        aesop
      · have h_contradiction : ¬ Even (padicValInt p v) → False := by
          intro h_odd
          have := p_mod4_eq1_of_dvd_v_not_dvd_m p q b h x y v R m hp hp2 hv_def hbqm hRv
            (by exact h_odd) (by exact_mod_cast hpm)
          cases this.symm.trans hp3
        simp_all +decide only [Int.reduceNeg, neg_mul, Nat.not_even_iff_odd,
          imp_false, Nat.not_odd_iff_even, ne_eq, hv_pos.ne', not_false_eq_true,
          padicValNat.mul]
        simp_all only [← hv_def, padicValInt.of_nat]
        rw [padicValNat.eq_zero_of_not_dvd] <;> simp_all +decide [Nat.prime_dvd_prime_iff_eq]
    · rw [padicValNat.eq_zero_of_not_dvd] <;> norm_num
      exact fun h => hpv <| Int.natCast_dvd_natCast.mpr <| hp.dvd_mul.mp h |> Or.resolve_left <| by
        intro t
        have := Nat.le_of_dvd (by positivity) t
        interval_cases p <;> trivial

lemma two_v_sum_two_squares (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hm_sq : Squarefree m)
    (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * ↑q) ↑p = 1) :
    ∃ a b : ℕ, 2 * v = a ^ 2 + b ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro p hp hp3
  exact even_padicVal_of_mod4_eq3 p q b h x y R v m (Nat.prime_of_mem_primeFactors hp) hp3
    hm_sq hv_pos hv_def hbqm hRv hjac


/-- The `m ≡ 3 (mod 8)` case of the three-squares theorem. -/
theorem blueprint_case_mod8_eq3 (m : ℕ) (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hm_mod : m % 8 = 3) : IsSumOfThreeSquares m := by
  obtain ⟨q, b, h, x, y, R, v, hq_prime, hq_mod, hjac, hbqm, hv_def, hRv, hv_pos⟩ :=
    exists_R_v_of_mod8_eq3 m hm_sq hm_pos hm_mod
  have h2v := two_v_sum_two_squares q b h x y R v m hm_sq hv_pos hv_def hbqm hRv hjac
  have habc : ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
    obtain ⟨A, B, hAB⟩ := h2v
    refine ⟨R, A, B, ?_⟩
    have hAB_int : (2 * v : ℤ) = (A : ℤ) ^ 2 + (B : ℤ) ^ 2 := by
      exact_mod_cast hAB
    nlinarith [hRv, hAB_int]
  obtain ⟨a, b, c, habc⟩ := habc
  refine ⟨a.natAbs, b.natAbs, c.natAbs, ?_⟩
  apply Int.ofNat.inj
  calc
    ((a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 : ℕ) : ℤ)
        = a ^ 2 + b ^ 2 + c ^ 2 := by
          norm_num [Int.natCast_natAbs, sq_abs]
    _ = (m : ℤ) := by simpa using habc.symm

end LeanPool.SumsThreeSquares
