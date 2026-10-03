/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Contour.Shift
public import Mathlib.Analysis.PSeries

/-! Moments of the logistic functional `E[φ] = ∫ φ(1/2 + iy) ρ(y) dy` (the proof notes, §0, §5.1):
`E[t^m] = B_m` (Bernoulli numbers with `B₁ = +1/2`, i.e. `bernoulli'`), and for `j ≥ 0`, `p ≥ 0`,
`E[(t+j)^{-(p+1)}] = (p+1) (ζ(p+2) − H_j^{(p+2)})`.
Both follow from the shift rule `E[F(t+1)] − E[F(t)] = F'(1)` alone. -/

public section

open MeasureTheory Set Filter Topology Finset

namespace Zeta32.Analytic.Contour

noncomputable section

/-- The logistic functional. -/
def Erho (φ : ℂ → ℂ) : ℂ := ∫ y : ℝ, φ (tpt y) * (rho y : ℂ)

lemma norm_tpt_le (y : ℝ) : ‖tpt y‖ ≤ 1 + |y| := by
  have h := Complex.norm_le_abs_re_add_abs_im (tpt y)
  rw [tpt_re, tpt_im] at h
  have : |(1/2 : ℝ)| = 1/2 := abs_of_pos (by norm_num)
  linarith

lemma norm_le_of_strip {t : ℂ} (h1 : 1 / 2 ≤ t.re) (h2 : t.re ≤ 3 / 2) : ‖t‖ ≤ 2 * (1 + |t.im|)
  := by
  have h := Complex.norm_le_abs_re_add_abs_im t
  have : |t.re| ≤ 3/2 := abs_le.mpr ⟨by linarith, h2⟩
  have := abs_nonneg t.im
  linarith

lemma polyGrowth_pow (m : ℕ) : PolyGrowth (fun t => t ^ m) (2 ^ m) m := by
  intro t h1 h2
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_of_strip h1 h2) m

lemma integrable_pow_rho (m : ℕ) : Integrable (fun y : ℝ => tpt y ^ m * (rho y : ℂ)) :=
  integrable_mul_rho (C := 1) (N := m) (continuous_tpt.pow m) fun y => by
    rw [norm_pow, one_mul]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_tpt_le y) m

/-- The recursion `Σ_{k<m} C(m,k) E[t^k] = m`. -/
lemma Erho_pow_recursion (m : ℕ) :
    ∑ k ∈ range m, ((m.choose k : ℕ) : ℂ) * Erho (fun t => t ^ k) = m := by
  cases m with
  | zero => simp
  | succ n =>
    have hs := shift_rule (F := fun t : ℂ => t ^ (n + 1))
      ((differentiable_id.pow _).differentiableOn) (polyGrowth_pow (n + 1))
    have hd : deriv (fun t : ℂ => t ^ (n + 1)) 1 = ((n + 1 : ℕ) : ℂ) := by
      rw [deriv_pow_field]; push_cast; ring
    rw [hd] at hs
    have hexp : ∀ y : ℝ, (tpt y + 1) ^ (n + 1) * (rho y : ℂ) =
        ∑ k ∈ range (n + 1 + 1), ((n + 1).choose k : ℂ) * (tpt y ^ k * (rho y : ℂ)) := by
      intro y
      rw [add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_pow, mul_one]; ring
    have hL : (∫ y : ℝ, (tpt y + 1) ^ (n + 1) * (rho y : ℂ)) =
        ∑ k ∈ range (n + 1 + 1), ((n + 1).choose k : ℂ) * Erho (fun t => t ^ k) := by
      simp_rw [hexp]
      rw [integral_finsetSum _ fun k _ => (integrable_pow_rho k).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]; rfl
    change (∫ y : ℝ, (tpt y + 1) ^ (n + 1) * (rho y : ℂ)) - Erho (fun t => t ^ (n + 1)) = _ at hs
    rw [hL, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, add_sub_cancel_right]
      at hs
    rw [hs]

/-- **Polynomial moments**: `E[t^m] = B_m` with `B₁ = +1/2`. -/
theorem Erho_pow (m : ℕ) : Erho (fun t => t ^ m) = (bernoulli' m : ℂ) := by
  induction m using Nat.strong_induction_on with
  | _ n ih =>
    have hA := Erho_pow_recursion (n + 1)
    have hB : ∑ k ∈ range (n + 1), (((n + 1).choose k : ℕ) : ℂ) * (bernoulli' k : ℂ) =
        ((n + 1 : ℕ) : ℂ) := by
      have := congrArg (fun q : ℚ => (q : ℂ)) (sum_bernoulli' (n + 1))
      push_cast at this ⊢
      exact this
    rw [Finset.sum_range_succ] at hA hB
    have hsame : ∑ k ∈ range n, (((n + 1).choose k : ℕ) : ℂ) * Erho (fun t => t ^ k) =
        ∑ k ∈ range n, (((n + 1).choose k : ℕ) : ℂ) * (bernoulli' k : ℂ) :=
      Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk)]
    have hc : (((n + 1).choose n : ℕ) : ℂ) ≠ 0 := by
      rw [Nat.choose_succ_self_right]; exact_mod_cast Nat.succ_ne_zero n
    apply mul_left_cancel₀ hc
    linear_combination hA - hB - hsame

/-! ### Poles -/

/-- `(t + j)^{-(p+1)}`. -/
def invPow (j p : ℕ) (t : ℂ) : ℂ := ((t + j) ^ (p + 1))⁻¹

lemma add_nat_re (t : ℂ) (j : ℕ) : (t + j).re = t.re + j := by simp

lemma norm_add_nat_ge {t : ℂ} (j : ℕ) : t.re + j ≤ ‖t + j‖ := by
  rw [← add_nat_re]; exact Complex.re_le_norm _

lemma add_nat_ne_zero {t : ℂ} (ht : 0 < t.re) (j : ℕ) : t + j ≠ 0 := by
  intro h
  have := norm_add_nat_ge (t := t) j
  rw [h, norm_zero] at this
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma differentiableOn_invPow (j p : ℕ) : DifferentiableOn ℂ (invPow j p) strip := by
  intro t ht
  apply DifferentiableAt.differentiableWithinAt
  unfold invPow
  exact ((differentiableAt_id.add_const _).pow _).inv (pow_ne_zero _ (add_nat_ne_zero ht.1 j))

lemma norm_invPow_le {t : ℂ} (ht : 1 / 2 ≤ t.re) (j p : ℕ) : ‖invPow j p t‖ ≤ 2 ^ (p + 1) := by
  unfold invPow
  rw [norm_inv, norm_pow, ← inv_pow]
  have h := norm_add_nat_ge (t := t) j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h2 : ‖t + j‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) h2 _

lemma polyGrowth_invPow (j p : ℕ) : PolyGrowth (invPow j p) (2 ^ (p + 1)) 0 := by
  intro t h1 _
  rw [pow_zero, mul_one]
  exact norm_invPow_le h1 j p

lemma norm_invPow_tpt_le (j p : ℕ) (hj : 1 ≤ j) (y : ℝ) :
    ‖invPow j p (tpt y)‖ ≤ 1 / (j : ℝ) := by
  unfold invPow
  rw [norm_inv, norm_pow]
  have h := norm_add_nat_ge (t := tpt y) j
  rw [tpt_re] at h
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : 1 ≤ ‖tpt y + j‖ := by linarith
  have h2 : (j : ℝ) ≤ ‖tpt y + j‖ ^ (p + 1) :=
    (by linarith : (j : ℝ) ≤ ‖tpt y + j‖).trans (le_self_pow₀ h1 (Nat.succ_ne_zero p))
  rw [one_div]
  exact inv_anti₀ (by linarith) h2

lemma invPow_add_one (j p : ℕ) (t : ℂ) : invPow j p (t + 1) = invPow (j + 1) p t := by
  unfold invPow; push_cast; ring_nf

lemma hasDerivAt_invPow (j p : ℕ) :
    HasDerivAt (invPow j p) (-((p + 1 : ℕ) : ℂ) / ((1 : ℂ) + j) ^ (p + 2)) 1 := by
  have hne : (1 : ℂ) + j ≠ 0 := add_nat_ne_zero (by norm_num) j
  have h0 : HasDerivAt (fun t : ℂ => t + j) 1 1 := (hasDerivAt_id (1 : ℂ)).add_const _
  have h := (h0.fun_pow (p + 1)).inv (pow_ne_zero _ hne)
  unfold invPow
  convert h using 1
  simp only [Nat.add_sub_cancel, mul_one]
  field_simp
  ring

lemma integrable_invPow_rho (j p : ℕ) : Integrable (fun y : ℝ => invPow j p (tpt y) * (rho y :
  ℂ)) :=
  integrable_mul_rho ((differentiableOn_invPow j p).continuousOn.comp_continuous continuous_tpt
    tpt_mem_strip) (polyGrowth_line (polyGrowth_invPow j p))

lemma integrable_rho : Integrable rho := by
  have h := (integrable_one_add_abs_pow_exp 0 (b := 2 * Real.pi) (by positivity)).const_mul
    (2 * Real.pi)
  refine h.mono' continuous_rho.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (rho_pos y)]
  simpa using rho_le y

lemma norm_Erho_le {φ : ℂ → ℂ} {c : ℝ} (h : ∀ y, ‖φ (tpt y)‖ ≤ c) :
    ‖Erho φ‖ ≤ c * ∫ y, rho y := by
  unfold Erho
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (integrable_rho.const_mul c) (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rho_pos y)]
  exact mul_le_mul_of_nonneg_right (h y) (rho_pos y).le

/-- The pole recursion `E[(t+j+1)^{-(p+1)}] = E[(t+j)^{-(p+1)}] − (p+1)/(j+1)^{p+2}`. -/
lemma Erho_invPow_succ (j p : ℕ) :
    Erho (invPow (j + 1) p) = Erho (invPow j p) - ((p + 1 : ℕ) : ℂ) / ((j + 1 : ℕ) : ℂ) ^ (p +
      2) := by
  have hs := shift_rule (differentiableOn_invPow j p) (polyGrowth_invPow j p)
  rw [(hasDerivAt_invPow j p).deriv] at hs
  simp only [invPow_add_one] at hs
  change Erho (invPow (j + 1) p) - Erho (invPow j p) = _ at hs
  rw [sub_eq_iff_eq_add'.mp hs]
  push_cast
  ring

/-- Real `p`-series tail term `1/(k + j + 1)^s`. -/
def tailTerm (s j k : ℕ) : ℝ := 1 / ((k : ℝ) + j + 1) ^ s

lemma Erho_invPow_telescope (j p N : ℕ) :
    Erho (invPow j p) = Erho (invPow (j + N) p) +
      ((p + 1 : ℕ) : ℂ) * ∑ k ∈ range N, (tailTerm (p + 2) j k : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, ← add_assoc j N 1, Erho_invPow_succ (j + N) p]
    unfold tailTerm
    push_cast
    ring

lemma summable_zetaTerm {s : ℕ} (hs : 1 < s) : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr hs)
  refine this.congr fun k => ?_
  push_cast; ring

lemma H_eq_sum_range (e j : ℕ) :
    ((H e j : ℚ) : ℝ) = ∑ i ∈ range j, 1 / ((i : ℝ) + 1) ^ e := by
  induction j with
  | zero => simp [H]
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold H
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    ring

/-- `Σ_{k ≥ 0} 1/(k+j+1)^s = ζ(s) − H_j^{(s)}` with `ζ(s)` written as a `tsum`. -/
lemma tsum_tailTerm {s : ℕ} (hs : 1 < s) (j : ℕ) :
    ∑' k, tailTerm s j k = (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s) - ((H s j : ℚ) : ℝ) := by
  rw [H_eq_sum_range, ← (summable_zetaTerm hs).sum_add_tsum_nat_add j, add_sub_cancel_left]
  refine tsum_congr fun k => ?_
  unfold tailTerm
  push_cast
  ring

/-- **Pole moments** `E[(t+j)^{-(p+1)}] = (p+1)(ζ(p+2) − H_j^{(p+2)})`. -/
theorem Erho_invPow (j p : ℕ) :
    Erho (invPow j p) = ((p + 1 : ℕ) : ℂ) *
      (((∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (p + 2)) - ((H (p + 2) j : ℚ) : ℝ) : ℝ) : ℂ) := by
  have hsum : Summable (tailTerm (p + 2) j) := by
    have := (summable_nat_add_iff (j + 1)).mpr (Real.summable_one_div_nat_pow.mpr
      (by omega : 1 < p + 2))
    refine this.congr fun k => ?_
    unfold tailTerm; push_cast; ring_nf
  rw [← tsum_tailTerm (by omega) j]
  -- `E[(t+j+N)^{-(p+1)}] → 0`
  have hdecay : Tendsto (fun N : ℕ => Erho (invPow (j + N) p)) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => (∫ y, rho y) * (1 / (N : ℝ))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul (∫ y, rho y)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hjN : 1 ≤ j + N := by omega
    have h1 := norm_Erho_le (φ := invPow (j + N) p) (norm_invPow_tpt_le (j + N) p hjN)
    have hI : 0 ≤ ∫ y, rho y := integral_nonneg fun y => (rho_pos y).le
    have h2 : 1 / ((j + N : ℕ) : ℝ) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast hN) (by exact_mod_cast Nat.le_add_left N j)
    calc ‖Erho (invPow (j + N) p)‖ ≤ 1 / ((j + N : ℕ) : ℝ) * ∫ y, rho y := h1
      _ ≤ 1 / (N : ℝ) * ∫ y, rho y := mul_le_mul_of_nonneg_right h2 hI
      _ = _ := by ring
  have hpart : Tendsto (fun N : ℕ => ((p + 1 : ℕ) : ℂ) * ∑ k ∈ range N, (tailTerm (p + 2) j k : ℂ))
      atTop (𝓝 (Erho (invPow j p))) := by
    have := (tendsto_const_nhds (x := Erho (invPow j p))).sub hdecay
    rw [sub_zero] at this
    refine this.congr fun N => ?_
    rw [Erho_invPow_telescope j p N]; ring
  have hlim : Tendsto (fun N : ℕ => ((p + 1 : ℕ) : ℂ) * ∑ k ∈ range N, (tailTerm (p + 2) j k : ℂ))
      atTop (𝓝 (((p + 1 : ℕ) : ℂ) * ((∑' k, tailTerm (p + 2) j k : ℝ) : ℂ))) := by
    refine Tendsto.const_mul _ ?_
    have := (Complex.continuous_ofReal.tendsto _).comp hsum.hasSum.tendsto_sum_nat
    refine this.congr fun N => ?_
    simp
  exact tendsto_nhds_unique hpart hlim

end

end Zeta32.Analytic.Contour

end
