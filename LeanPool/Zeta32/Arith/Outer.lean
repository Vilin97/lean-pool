/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Profiles
public import LeanPool.Zeta32.Arith.Outer.Norm

/-! the proof notes, §4 Lemma 5 and §8.2 Lemma 9: for every prime `p` with `7n < 3p ≤ 15n`, `p ∤
den r`,
  `cost r n p ≤ n φ(p/n) + 5`.
The Gauss bound `outer_valuation_bound` is Lemma 5 with the class costs of Lemma 9 inserted; the
arithmetic comparison with `n φ(p/n)` is `outer_arith`. Both hold for every `n` (the hypotheses
force
`n ≥ 1`, `p ≥ 3`, `p > 2n`, `p² > 5n`); `outer_per_prime_bound` is the eventual form used by
`Arith.arith_of_parts`. -/

public section

open Zeta32.Arith.Local
namespace Zeta32.Outer
open Polynomial

/-- `cost` is bounded by minus any Gauss lower bound of the nonzero `Qtilde`. -/
theorem cost_le_of_GV {r : ℚ} {n p : ℕ} {B : ℚ} (hQ : Qtilde r n ≠ 0)
    (h : GV p (Qtilde r n) B) : cost r n p ≤ -(B:ℝ) := by
  unfold cost
  apply neg_le_neg
  apply le_csInf
  · exact ⟨_, (Qtilde r n).natDegree, leadingCoeff_ne_zero.mpr hQ, rfl⟩
  · rintro v ⟨k, hk, rfl⟩
    have := (h k).resolve_left hk
    exact_mod_cast this

lemma Qtilde_ne_zero {r : ℚ} {n : ℕ} (hQ : Q r n ≠ 0) : Qtilde r n ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr (scale_pos n).ne') hQ

end Zeta32.Outer

namespace Zeta32.Arith

open Polynomial Zeta32.Outer

/-- The outer class sum, `Σ_c gcl`, in closed form. -/
def outerClassBound (n p : ℕ) : ℚ :=
  -4 - ((5*n - 2*p : ℕ) : ℚ) - 4 * ((min (p - 1 - n) (5*n - p - n) : ℕ) : ℚ)

/-- the proof notes, Lemma 5 (with Lemma 9's class costs) in the outer range: every coefficient
of `Qtilde r n`
has `v_p ≥ normVal + Σ_classes - r_p`, `r_p = 5n + 1 - p`. -/
theorem outer_valuation_bound (r : ℚ) (n p : ℕ) (hp : p.Prime) (h73 : 7 * n < 3 * p) (hp5 : p ≤
  5 * n)
    (hden : ¬ p ∣ r.den) :
    GV p (Qtilde r n) (normVal p n + outerClassBound n p - ((5*n + 1 - p : ℕ) : ℚ)) := by
  have := Fact.mk hp
  have hp2l := hp.two_le
  have hp2 : p ≠ 2 := by omega
  have hr := VG_of_not_dvd_den (p := p) hden
  have hK : 5*n < p^2 := by
    have h1 : 7*n + 1 ≤ 3*p := h73
    nlinarith
  have hraw := scaled_Q_GV hp2 hr n hK
  rw [rowScale_prod (by omega) (by omega)] at hraw
  have hS : ∑ c : Fin p, gcl n p c ≤ ∑ c : Fin p, Scl n p c :=
    Finset.sum_le_sum fun c _ => Scl_ge_gcl h73 hp5 c.isLt
  rw [sum_gcl h73 hp5] at hS
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hQ : GV p (Q r n) (-((5*n+1-p : ℕ):ℚ) + ∑ c : Fin p, Scl n p c) := by
    have e : Q r n = C ((p:ℚ)^(-((5*n+1-p : ℕ) : ℤ))) * (C ((p:ℚ)^(5*n+1-p)) * Q r n) := by
      rw [← mul_assoc, ← C_mul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hpq), C_1,
        one_mul]
    rw [e]
    have := GV.C_mul (VG.primePow (p := p) (-((5*n+1-p : ℕ) : ℤ))) hraw
    simpa using this
  have hQt := GV.C_mul (scale_VG p hK) hQ
  change GV p (Qtilde r n) _ at hQt
  refine hQt.mono ?_
  unfold outerClassBound
  linarith

/-- The comparison of Lemma 9 with `n φ(p/n) + 5`, term by term on the four pieces of `φ`. -/
theorem outer_arith (n p : ℕ) (h73 : 7 * n < 3 * p) (hp5 : p ≤ 5 * n) :
    -(((normVal p n + outerClassBound n p - ((5*n + 1 - p : ℕ) : ℚ)) : ℚ) : ℝ) ≤
      n * ArithSum.phiL ((p:ℝ)/(n:ℝ)) + 5 := by
  have hp0 : 0 < p := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hnp : n / p = 0 := Nat.div_eq_of_lt (by omega)
  have hσ := floor_sum_small (n := n) hp0 (by omega)
  have hR : (5*n + 1 - p) + p = 5*n + 1 := by omega
  have hRq : (((5*n + 1 - p : ℕ)) : ℚ) + p = 5*n + 1 := by exact_mod_cast hR
  unfold normVal outerClassBound
  rw [hnp, hσ]
  suffices key : ∃ E : ℚ,
      -(3 * (n:ℚ) * (((5*n/p : ℕ) : ℚ) - 4 * ((0:ℕ):ℚ)) - 2 * ((3*n - p : ℕ) : ℚ) +
        (-4 - ((5*n - 2*p : ℕ) : ℚ) - 4 * ((min (p - 1 - n) (5*n - p - n) : ℕ) : ℚ)) -
        ((5*n + 1 - p : ℕ) : ℚ)) ≤ E ∧
      (E : ℝ) = n * ArithSum.phiL ((p:ℝ)/(n:ℝ)) + 5 by
    obtain ⟨E, h1, h2⟩ := key
    rw [← h2]
    exact_mod_cast h1
  unfold ArithSum.phiL
  by_cases hA : 2*p ≤ 5*n
  · -- (7/3, 5/2]: L = 2, M = 1
    have hL : 5*n/p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h3 : (3*n - p) + p = 3*n := by omega
    have ha : (5*n - 2*p) + 2*p = 5*n := by omega
    have hm : min (p - 1 - n) (5*n - p - n) + 1 + n = p := by omega
    have h3q : ((3*n - p : ℕ) : ℚ) + p = 3*n := by exact_mod_cast h3
    have haq : ((5*n - 2*p : ℕ) : ℚ) + 2*p = 5*n := by exact_mod_cast ha
    have hmq : ((min (p - 1 - n) (5*n - p - n) : ℕ) : ℚ) + 1 + n = p := by exact_mod_cast hm
    refine ⟨6*n - p + 5, ?_, ?_⟩
    · rw [hL]; push_cast at hmq ⊢; linarith
    · have hx : (p:ℝ)/n ≤ 5/2 := by
        rw [div_le_iff₀ hnR]; have : (2*p:ℝ) ≤ 5*n := by exact_mod_cast hA
        linarith
      rw [ite_eq_left hx]; push_cast; field_simp
  · by_cases hB : p ≤ 3*n
    · -- (5/2, 3]: L = 1, M = 1
      have hL : 5*n/p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have h3 : (3*n - p) + p = 3*n := by omega
      have ha : 5*n - 2*p = 0 := by omega
      have hm : min (p - 1 - n) (5*n - p - n) + p = 4*n := by omega
      have h3q : ((3*n - p : ℕ) : ℚ) + p = 3*n := by exact_mod_cast h3
      have hmq : ((min (p - 1 - n) (5*n - p - n) : ℕ) : ℚ) + p = 4*n := by exact_mod_cast hm
      refine ⟨24*n - 7*p + 5, ?_, ?_⟩
      · rw [hL, ha]; push_cast at hmq ⊢; linarith
      · have hx1 : ¬ (p:ℝ)/n ≤ 5/2 := by
          rw [div_le_iff₀ hnR]; have : (5*n:ℝ) < 2*p := by exact_mod_cast (by omega : 5*n < 2*p)
          linarith
        have hx2 : (p:ℝ)/n ≤ 3 := by
          rw [div_le_iff₀ hnR]; exact_mod_cast hB
        rw [ite_eq_right hx1, ite_eq_left hx2]; push_cast; field_simp
    · by_cases hC : p ≤ 4*n
      · -- (3, 4]: L = 1, M = 0
        have hL : 5*n/p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        have h3 : 3*n - p = 0 := by omega
        have ha : 5*n - 2*p = 0 := by omega
        have hm : min (p - 1 - n) (5*n - p - n) + p = 4*n := by omega
        have hmq : ((min (p - 1 - n) (5*n - p - n) : ℕ) : ℚ) + p = 4*n := by exact_mod_cast hm
        refine ⟨18*n - 5*p + 5, ?_, ?_⟩
        · rw [hL, ha, h3]; push_cast at hmq ⊢; linarith
        · have hx1 : ¬ (p:ℝ)/n ≤ 5/2 := by
            rw [div_le_iff₀ hnR]; have : (5*n:ℝ) < 2*p := by exact_mod_cast (by omega : 5*n < 2*p)
            linarith
          have hx2 : ¬ (p:ℝ)/n ≤ 3 := by
            rw [div_le_iff₀ hnR]; have : (3*n:ℝ) < p := by exact_mod_cast (by omega : 3*n < p)
            linarith
          have hx3 : (p:ℝ)/n ≤ 4 := by
            rw [div_le_iff₀ hnR]; exact_mod_cast hC
          rw [ite_eq_right hx1, ite_eq_right hx2, ite_eq_left hx3]; push_cast; field_simp
      · -- (4, 5]: L = 1, M = 0
        have hL : 5*n/p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        have h3 : 3*n - p = 0 := by omega
        have ha : 5*n - 2*p = 0 := by omega
        have hm : min (p - 1 - n) (5*n - p - n) = 0 := by omega
        refine ⟨2*n - p + 5, ?_, ?_⟩
        · rw [hL, ha, h3, hm]; push_cast; linarith
        · have hx1 : ¬ (p:ℝ)/n ≤ 5/2 := by
            rw [div_le_iff₀ hnR]; have : (5*n:ℝ) < 2*p := by exact_mod_cast (by omega : 5*n < 2*p)
            linarith
          have hx2 : ¬ (p:ℝ)/n ≤ 3 := by
            rw [div_le_iff₀ hnR]; have : (3*n:ℝ) < p := by exact_mod_cast (by omega : 3*n < p)
            linarith
          have hx3 : ¬ (p:ℝ)/n ≤ 4 := by
            rw [div_le_iff₀ hnR]; have : (4*n:ℝ) < p := by exact_mod_cast (by omega : 4*n < p)
            linarith
          rw [ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hx3]; push_cast; field_simp

/-- Lemma 9 for one prime: `cost r n p ≤ n φ(p/n) + 5` for every `n`. -/
theorem outer_cost_bound (r : ℚ) (n p : ℕ) (hp : p.Prime) (h73 : 7 * n < 3 * p) (hp5 : p ≤ 5 * n)
    (hden : ¬ p ∣ r.den) (hQ : Q r n ≠ 0) :
    cost r n p ≤ n * ArithSum.phiL ((p:ℝ)/(n:ℝ)) + 5 :=
  (cost_le_of_GV (Qtilde_ne_zero hQ) (outer_valuation_bound r n p hp h73 hp5 hden)).trans
    (outer_arith n p h73 hp5)

/-- the proof notes, §8.2, Lemma 9, in the form used by `ArithSum.arith_sum` (hypothesis `h2`). -/
theorem outer_per_prime_bound (r : ℚ) : ∀ᶠ n : ℕ in Filter.atTop, ∀ p : ℕ, p.Prime →
    7*n < 3*p → p ≤ 5*n → ¬ p ∣ r.den → Q r n ≠ 0 →
    cost r n p ≤ n * ArithSum.phiL ((p:ℝ)/(n:ℝ)) + 5 :=
  Filter.Eventually.of_forall fun n p hp h73 hp5 hden hQ =>
    outer_cost_bound r n p hp h73 hp5 hden hQ

end Zeta32.Arith
end
