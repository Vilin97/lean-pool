/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Pointwise
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! the proof notes (6′): the scaling `y = n x` of the Heine integral.

`∫_{ℝ^h} heine(y) dy = n^h ∫ heine(n x) dx`, `Δ(n x)² = n^{h(h−1)} Δ(x)²`, and (5′) per
coordinate; with
`log F_n ≥ h² log h − (3/2)h² − 2h log h` this gives
`|Q_n(C_r)| ≤ exp(9(3/2 − log 3)n² + C n log(n+1)) ∫ D` for every integrable `D` dominating
`∏_l (1+|x_l|)^7 e^{−3n W(x_l)} · Δ(x)²`. -/

public section

open Real MeasureTheory Polynomial
open scoped BigOperators

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-- The squared Vandermonde product in the form of `heineIntegrand`. -/
@[expose]
def vdm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l') ^ 2

theorem vdm_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ vdm x :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem sum_card_filter_lt (m : ℕ) :
    (∑ l : Fin m, (Finset.univ.filter (fun l' => l < l')).card) * 2 = m * (m - 1) := by
  have e : ∀ l : Fin m, (Finset.univ.filter (fun l' => l < l')).card = m - 1 - (l : ℕ) := by
    intro l
    rw [show Finset.univ.filter (fun l' => l < l') = Finset.Ioi l by ext; simp, Fin.card_Ioi]
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m, Finset.sum_range_reflect (fun i => i) m,
    Finset.sum_range_id_mul_two]

theorem vdm_smul {m : ℕ} (c : ℝ) (x : Fin m → ℝ) : vdm (c • x) = c ^ (m * (m - 1)) * vdm x := by
  unfold vdm
  have e : ∀ l : Fin m, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), ((c • x) l - (c • x) l') ^ 2 =
      (c ^ 2) ^ (Finset.univ.filter (fun l' => l < l')).card *
        ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l') ^ 2 := by
    intro l
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l' _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm 2,
    sum_card_filter_lt]

theorem heineIntegrand_eq (r : ℚ) (n : ℕ) (y : Fin (3 * n) → ℝ) :
    heineIntegrand r n y = (∏ l, psiH r n (y l)) * vdm y := rfl

/-- (5′)+(6′): the Heine bound after scaling, with the external field `nV = −h W`. -/
theorem heine_scaled (r : ℚ) : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → HeineBound r n →
    ∀ D : (Fin (3*n) → ℝ) → ℝ, Integrable D →
      (∀ x : Fin (3*n) → ℝ, (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) *
          ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2 ≤ D x) →
      |aeval (Cr r) (Qtilde r n)| ≤
        Real.exp (9 * (3/2 - Real.log 3) * (n:ℝ)^2 + C * (n:ℝ) * Real.log ((n:ℝ) + 1)) *
          ∫ x, D x := by
  refine ⟨6 * |cPt r| + 51, fun n hn hH D hD hGD => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hS : 0 < (Sn n : ℝ) := by exact_mod_cast Sn_pos n
  have hF : 0 < (Fn n : ℝ) := by exact_mod_cast Fn_pos n
  set E := Real.exp (cPt r + 7 * Real.log ((n : ℝ) + 1)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hG0 : ∀ x : Fin (3 * n) → ℝ, 0 ≤ (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x
    l|))) * vdm x :=
    fun x => mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (vdm_nonneg x)
  have hD0 : 0 ≤ ∫ x, D x := integral_nonneg fun x => (hG0 x).trans (hGD x)
  -- the value
  have hval : |aeval (Cr r) (Qtilde r n)| = (scale n : ℝ) * |aeval (Cr r) (Q r n)| := by
    rw [Qtilde, map_mul, aeval_C, abs_mul, eq_ratCast, abs_of_pos (by exact_mod_cast scale_pos n)]
  -- the scaling of the integral
  have hscale : ∫ y, heineIntegrand r n y = (n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ)
    • x) := by
    rw [Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul]
    rw [abs_of_pos (by positivity), ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  -- pointwise
  have hpt : ∀ x : Fin (3 * n) → ℝ, (Sn n : ℝ) ^ (3 * n) * heineIntegrand r n ((n : ℝ) • x) ≤
      E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * D x := by
    intro x
    rw [heineIntegrand_eq, vdm_smul]
    have hprod : (Sn n : ℝ) ^ (3 * n) * ∏ l, psiH r n (((n : ℝ) • x) l) =
        ∏ l, ((Sn n : ℝ) * psiH r n ((n : ℝ) * x l)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl
    have hle : ∏ l, ((Sn n : ℝ) * psiH r n ((n : ℝ) * x l)) ≤
        ∏ l, (E * ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) :=
      Finset.prod_le_prod₀ (fun l _ => mul_nonneg hS.le (psiH_nonneg r n _))
        (fun l _ => pointwise_bound r n hn (x l))
    have hR : ∏ l, (E * ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) =
        E ^ (3 * n) * ∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    replace hle := hle.trans hR.le
    have hG := hGD x
    change (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) * vdm x ≤ D x at hG
    calc (Sn n : ℝ) ^ (3 * n) * ((∏ l, psiH r n (((n : ℝ) • x) l)) * ((n : ℝ) ^ ((3 * n) * ((3 *
      n) - 1)) * vdm x))
        = (∏ l, ((Sn n : ℝ) * psiH r n ((n : ℝ) * x l))) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) *
          vdm x := by
          rw [← hprod]; ring
      _ ≤ (E ^ (3 * n) * ∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) *
          (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * vdm x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (by positivity)) (vdm_nonneg x)
      _ = E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) *
          ((∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) * vdm x) := by ring
      _ ≤ E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * D x :=
          mul_le_mul_of_nonneg_left hG (by positivity)
  have hint : ∫ x, (Sn n : ℝ) ^ (3 * n) * heineIntegrand r n ((n : ℝ) • x) ≤
      E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * ∫ x, D x := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hD.const_mul _)
      (Filter.Eventually.of_forall hpt)
    change 0 ≤ (Sn n : ℝ) ^ (3 * n) * heineIntegrand r n ((n : ℝ) • x)
    rw [heineIntegrand_eq]
    exact mul_nonneg (pow_nonneg hS.le _) (mul_nonneg (Finset.prod_nonneg fun _ _ => psiH_nonneg
      _ _ _)
      (vdm_nonneg _))
  -- the coefficient
  have hfact : (1 : ℝ) ≤ ((3 * n).factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
  have hscl : (scale n : ℝ) = (Sn n : ℝ) ^ (3 * n) / (Fn n : ℝ) := by
    simp only [scale, Rat.cast_div, Rat.cast_pow]
  have hmain : |aeval (Cr r) (Qtilde r n)| ≤
      ((n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1))) / (Fn n : ℝ)) * ∫
        x, D x := by
    rw [hval]
    have h1 := hH
    unfold HeineBound at h1
    rw [hscale] at h1
    have h2 : |aeval (Cr r) (Q r n)| ≤ (n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x)
      := by
      refine h1.trans ?_
      have hI0 : 0 ≤ ∫ x, heineIntegrand r n ((n : ℝ) • x) :=
        integral_nonneg fun x => by
          rw [heineIntegrand_eq]
          exact mul_nonneg (Finset.prod_nonneg fun _ _ => psiH_nonneg _ _ _) (vdm_nonneg _)
      have : 1 / ((3 * n).factorial : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hfact
      have hp : 0 ≤ (n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x) := by positivity
      calc 1 / ((3 * n).factorial : ℝ) * ((n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x))
          ≤ 1 * ((n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x)) :=
            mul_le_mul_of_nonneg_right this hp
        _ = _ := one_mul _
    have h3 : (Sn n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n : ℝ) • x) ≤
        E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) * ∫ x, D x := by
      rw [← integral_const_mul]; exact hint
    rw [hscl]
    calc (Sn n : ℝ) ^ (3 * n) / (Fn n : ℝ) * |aeval (Cr r) (Q r n)|
        ≤ (Sn n : ℝ) ^ (3 * n) / (Fn n : ℝ) * ((n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n :
          ℝ) • x)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (n : ℝ) ^ (3 * n) / (Fn n : ℝ) * ((Sn n : ℝ) ^ (3 * n) * ∫ x, heineIntegrand r n ((n :
        ℝ) • x)) := by
          ring
      _ ≤ (n : ℝ) ^ (3 * n) / (Fn n : ℝ) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) *
        ∫ x, D x) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hD0)
  -- logarithmic bound on the coefficient
  have hpos : 0 < (n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1))) / (Fn
    n : ℝ) := by positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have hhR : (((3 * n : ℕ)) : ℝ) = 3 * (n : ℝ) := by push_cast; ring
  have hexp_n : (n : ℝ) ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)) = (n : ℝ) ^ ((3 * n) *
    (3 * n)) := by
    rw [← pow_add]
    congr 1
    rcases Nat.eq_zero_or_pos (3 * n) with h0 | h0
    · rw [h0]
    · have : 3 * n ≤ 3 * n * (3 * n) := Nat.le_mul_of_pos_right _ h0
      rw [Nat.mul_sub_one]; omega
  have hlog : Real.log ((n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1)))
    / (Fn n : ℝ)) =
      (((3 * n) * (3 * n) : ℕ) : ℝ) * Real.log n + ((3 * n) : ℝ) * (cPt r + 7 * Real.log ((n :
        ℝ) + 1)) -
        Real.log (Fn n : ℝ) := by
    rw [show (n : ℝ) ^ (3 * n) * (E ^ (3 * n) * (n : ℝ) ^ ((3 * n) * ((3 * n) - 1))) = (n : ℝ) ^
      ((3 * n) * (3 * n)) * E ^ (3 * n) by
      rw [← hexp_n]; ring]
    rw [Real.log_div (by positivity) hF.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow,
      Real.log_pow, hE, Real.log_exp]
    push_cast; ring
  rw [hlog]
  have hFl := Fn_log_lower n hn
  have hlog3n : Real.log (((3 * n : ℕ)) : ℝ) = Real.log 3 + Real.log n := by
    rw [hhR, Real.log_mul (by norm_num) hn0.ne']
  rw [hlog3n, hhR] at hFl
  have hlogn : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have := Real.log_le_log (by norm_num : (0:ℝ) < 2) (show (2:ℝ) ≤ (n : ℝ) + 1 by linarith)
    norm_num at h2
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hcast : (((3 * n) * (3 * n) : ℕ) : ℝ) = 9 * (n : ℝ) ^ 2 := by push_cast; ring
  rw [hcast]
  have hc := le_abs_self (cPt r)
  have hca := abs_nonneg (cPt r)
  have hL := Real.log_nonneg (show (1:ℝ) ≤ (n : ℝ) + 1 by linarith)
  -- `n ≤ 2 n log(n+1)`, `n log n ≤ n log(n+1)`
  have k1 : (n : ℝ) ≤ 2 * ((n : ℝ) * Real.log ((n : ℝ) + 1)) := by
    have := mul_le_mul_of_nonneg_left hlog2 hn0.le
    linarith
  have k2 : (n : ℝ) * Real.log n ≤ (n : ℝ) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hlogn hn0.le
  have k3 : 3 * (n : ℝ) * cPt r ≤ 3 * |cPt r| * (2 * ((n : ℝ) * Real.log ((n : ℝ) + 1))) := by
    have a1 := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 3 * n by positivity)
    have a2 := mul_le_mul_of_nonneg_left k1 (show (0:ℝ) ≤ 3 * |cPt r| by positivity)
    linarith
  have k4 : (n : ℝ) * Real.log 3 ≤ 2 * (2 * ((n : ℝ) * Real.log ((n : ℝ) + 1))) := by
    have := mul_le_mul_of_nonneg_left hlog3 hn0.le
    linarith
  linarith

end
end Zeta32.Analytic.EnergyI

end
