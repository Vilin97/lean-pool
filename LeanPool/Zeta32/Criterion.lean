/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Positivity
import LeanPool.Zeta5Irrational.Criterion

/-! Generic criterion adapted from the Li₂ light-certificate project and the
Apéry criterion in mo271/Zeta5 (Apache-2.0), with attribution retained. -/

public section

open Polynomial Filter Topology
namespace Zeta32

lemma pow_mul_aeval_div_eq_intCast (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d) (a b : ℤ)
    (hb : b ≠ 0) :
    (b : ℝ) ^ d * aeval ((a : ℝ) / b) p =
      ((∑ k ∈ Finset.range (d + 1), p.coeff k * a ^ k * b ^ (d - k) : ℤ) : ℝ) :=
  Zeta5Irrational.pow_mul_aeval_div_eq_intCast p hd a b hb

theorem one_le_den_pow_mul_abs (Q : ℤ[X]) (q : ℚ) (d : ℕ)
    (hdeg : Q.natDegree ≤ d) (hne : aeval (q : ℝ) Q ≠ 0) :
    1 ≤ (q.den : ℝ)^d * |aeval (q : ℝ) Q| := by
  let m : ℤ := ∑ k ∈ Finset.range (d+1), Q.coeff k * q.num^k * (q.den : ℤ)^(d-k)
  have hb : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hm : (q.den : ℝ)^d * aeval (q : ℝ) Q = (m : ℝ) := by
    simpa [Rat.cast_def, Int.cast_natCast, m] using
      pow_mul_aeval_div_eq_intCast Q hdeg q.num (q.den : ℤ)
        (by exact_mod_cast q.den_pos.ne')
  have hm0 : m ≠ 0 := by
    intro hz
    have : (q.den : ℝ)^d * aeval (q : ℝ) Q = 0 := by simpa [hz] using hm
    exact hne ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hb.ne'))
  have hge : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
    exact_mod_cast this
  rw [← hm, abs_mul, abs_of_pos (pow_pos hb _)] at hge
  exact hge

theorem irrational_of_int_polynomials (ξ : ℝ) (P : ℕ → ℤ[X]) (d : ℕ → ℕ)
    (hdeg : ∀ n, (P n).natDegree ≤ d n)
    (hdecay : ∀ b : ℕ, 0 < b →
      Tendsto (fun n => (b : ℝ)^(d n) * |aeval ξ (P n)|) atTop (𝓝 0))
    (hnonzero : ∀ q : ℚ, ∃ᶠ n in atTop, aeval (q : ℝ) (P n) ≠ 0) :
    Irrational ξ := by
  rintro ⟨q, hq⟩
  have hsmall : ∀ᶠ n in atTop, (q.den : ℝ)^(d n) * |aeval ξ (P n)| < 1 :=
    (hdecay q.den q.den_pos).eventually (gt_mem_nhds one_pos)
  obtain ⟨n, hn, hs⟩ := ((hnonzero q).and_eventually hsmall).exists
  have hge := one_le_den_pow_mul_abs (P n) q (d n) (hdeg n) hn
  rw [hq] at hge
  linarith

theorem tendsto_pow_mul_exp_neg_sq_of_pos {c : ℝ} (hc : 0 < c) (D b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (D * n) * Real.exp (-c * (n : ℝ) ^ 2)) atTop (𝓝 0) :=
  Zeta5Irrational.tendsto_pow_mul_exp_neg_sq_of_pos_degree hc D b hb

end Zeta32
end
