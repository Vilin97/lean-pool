/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Polynomial.HollowBound
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace EGZ

/-- The filter for a natural number tending to infinity through prime values. -/
def atTopAlongPrimes : Filter ℕ :=
  Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}

/-- The upper-bound form used in Section 9 of the paper.  Together with the
elementary lower bound
`hollowConstant p d * (p - 1) + 1 ≤ egzConstant p d` and a bound on
`hollowConstant p d` that is uniform in `p` for fixed `d` (Proposition `thw`
in the paper), this implies the little-`o` formulation of Theorem 1.2. -/
def MainUpperBound (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ p in atTopAlongPrimes,
      (egzConstant p d : ℝ) ≤
        ((hollowConstant p d : ℝ) + ε) * (p : ℝ)

/-- The direct little-`o` formulation of Theorem 1.2. -/
def MainAsymptotic (d : ℕ) : Prop :=
  (fun p : ℕ =>
      (egzConstant p d : ℝ) -
        (p : ℝ) * (hollowConstant p d : ℝ)) =o[atTopAlongPrimes]
    (fun p : ℕ => (p : ℝ))

/-! ## Consequences of the polynomial bound -/

/-- The polynomial-method bound holds eventually (in fact, pointwise) along
the primes. -/
theorem eventually_hollowConstant_le_choose_add_one (d : ℕ) (hd : 1 ≤ d) :
    ∀ᶠ p in atTopAlongPrimes,
      hollowConstant p d ≤ (2 * d - 1).choose d + 1 := by
  rw [atTopAlongPrimes, Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall fun p hp ↦
    hollowConstant_le_choose_add_one hp hd

/-- A uniformly bounded real-valued function is `o(p)` as `p → ∞` along
the prime filter. -/
theorem isLittleO_natCast_of_eventually_norm_le {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ᶠ p in atTopAlongPrimes, ‖f p‖ ≤ C) :
    f =o[atTopAlongPrimes] (fun p : ℕ => (p : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_gt (C / c)
  have hNat : ∀ᶠ p : ℕ in atTopAlongPrimes, N ≤ p := by
    apply Filter.Eventually.filter_mono
      (show atTopAlongPrimes ≤ Filter.atTop by
        unfold atTopAlongPrimes
        exact inf_le_left)
    exact Filter.eventually_ge_atTop N
  filter_upwards [hC, hNat] with p hfp hp
  have hN' : C < c * (N : ℝ) := by
    rw [div_lt_iff₀ hc] at hN
    nlinarith
  have hp' : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hCp : C ≤ c * (p : ℝ) := by nlinarith
  calc
    ‖f p‖ ≤ C := hfp
    _ ≤ c * ‖(p : ℝ)‖ := by simpa using hCp

/-- The explicit lower benchmark furnished by an extremal hollow family. -/
noncomputable def elementaryHollowLowerBound (p d : ℕ) : ℕ :=
  hollowConstant p d * (p - 1) + 1

theorem elementaryHollowLowerBound_le_egzConstant {p d : ℕ} (hp : p.Prime) :
    elementaryHollowLowerBound p d ≤ egzConstant p d :=
  hollowConstant_mul_add_one_le_egzConstant hp

/-- The elementary hollow-family lower benchmark differs from `p * w` by
`o(p)`, thanks to the uniform polynomial-method bound on `w`. -/
theorem elementaryHollowLowerBound_error_isLittleO (d : ℕ) (hd : 1 ≤ d) :
    (fun p : ℕ =>
        (p : ℝ) * (hollowConstant p d : ℝ) -
          (elementaryHollowLowerBound p d : ℝ)) =o[atTopAlongPrimes]
      (fun p : ℕ => (p : ℝ)) := by
  apply isLittleO_natCast_of_eventually_norm_le
    (C := (((2 * d - 1).choose d + 1 : ℕ) : ℝ) + 1)
  rw [atTopAlongPrimes, Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall fun p hp ↦ by
    have hp1 : 1 ≤ p := hp.one_le
    have hw := hollowConstant_le_choose_add_one hp hd
    have hw' : (hollowConstant p d : ℝ) ≤
        (((2 * d - 1).choose d + 1 : ℕ) : ℝ) := by
      exact_mod_cast hw
    have heq :
        (p : ℝ) * (hollowConstant p d : ℝ) -
            (elementaryHollowLowerBound p d : ℝ) =
          (hollowConstant p d : ℝ) - 1 := by
      simp only [elementaryHollowLowerBound, Nat.cast_add, Nat.cast_mul,
        Nat.cast_one, Nat.cast_sub hp1]
      ring
    rw [heq, Real.norm_eq_abs]
    have hw0 : 0 ≤ (hollowConstant p d : ℝ) := by positivity
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/-! ## The asymptotic bridge -/

/-- The elementary lower bound gives the lower half of the asymptotic
squeeze. -/
theorem eventually_neg_mul_le_mainError (d : ℕ) (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTopAlongPrimes,
      -ε * (p : ℝ) ≤
        (egzConstant p d : ℝ) -
          (p : ℝ) * (hollowConstant p d : ℝ) := by
  let C : ℝ := (((2 * d - 1).choose d + 1 : ℕ) : ℝ)
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have hNat : ∀ᶠ p : ℕ in atTopAlongPrimes, N ≤ p := by
    apply Filter.Eventually.filter_mono
      (show atTopAlongPrimes ≤ Filter.atTop by
        unfold atTopAlongPrimes
        exact inf_le_left)
    exact Filter.eventually_ge_atTop N
  have hPrime : ∀ᶠ p : ℕ in atTopAlongPrimes, p.Prime := by
    rw [atTopAlongPrimes, Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall fun _p hp ↦ hp
  filter_upwards [eventually_hollowConstant_le_choose_add_one d hd, hNat, hPrime]
    with p hw hp hpPrime
  have hLower : hollowConstant p d * (p - 1) + 1 ≤ egzConstant p d :=
    hollowConstant_mul_add_one_le_egzConstant (d := d) hpPrime
  have hbase : hollowConstant p d * (p - 1) ≤ egzConstant p d := by
    omega
  have hmulNat : p * hollowConstant p d ≤
      egzConstant p d + hollowConstant p d := by
    calc
      p * hollowConstant p d =
          ((p - 1) + 1) * hollowConstant p d := by
        rw [Nat.sub_add_cancel hpPrime.one_le]
      _ = (p - 1) * hollowConstant p d + hollowConstant p d := by
        rw [Nat.add_mul, one_mul]
      _ = hollowConstant p d * (p - 1) + hollowConstant p d := by
        rw [Nat.mul_comm (p - 1)]
      _ ≤ egzConstant p d + hollowConstant p d :=
        Nat.add_le_add_right hbase _
  have hmul : (p : ℝ) * (hollowConstant p d : ℝ) ≤
      (egzConstant p d : ℝ) + (hollowConstant p d : ℝ) := by
    exact_mod_cast hmulNat
  have hw' : (hollowConstant p d : ℝ) ≤ C := by
    dsimp [C]
    exact_mod_cast hw
  have hN' : C < ε * (N : ℝ) := by
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  have hp' : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hCp : C ≤ ε * (p : ℝ) := by nlinarith
  nlinarith

/-- Once the paper's upper estimate is available, the elementary lower
estimate and the polynomial bound complete Theorem 1.2. -/
theorem mainAsymptotic_of_mainUpperBound (d : ℕ) (hd : 1 ≤ d)
    (hUpper : MainUpperBound d) : MainAsymptotic d := by
  rw [MainAsymptotic, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hUpper ε hε, eventually_neg_mul_le_mainError d hd hε]
    with p hUpperP hLowerP
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hright :
      (egzConstant p d : ℝ) -
          (p : ℝ) * (hollowConstant p d : ℝ) ≤
        ε * (p : ℝ) := by
    nlinarith
  have hleft :
      -(ε * (p : ℝ)) ≤
        (egzConstant p d : ℝ) -
          (p : ℝ) * (hollowConstant p d : ℝ) := by
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0]
  exact abs_le.2 ⟨hleft, hright⟩

end EGZ
