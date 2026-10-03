/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.DetIntegral
import LeanPool.Zeta5Irrational.HermiteIBP
import LeanPool.Zeta5Irrational.Moments
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # Towards the energy bound (6.14): elementary ingredients

* the external field `V(t) = 2π√t + ∫₀¹ log(t+u²) du - 6 ∫₀^α log(t+u²) du` of (6.1);
* the bound `w(y) ≤ (1/π) (1 + 2πy)^5 e^{-2πy}` (a form of (6.11));
* a variant of the sum–integral comparison (6.12) for `u ↦ log (t + u²)`, using
  `2 log(2K) + 2` in place of `2 log K + 2` in the upper error bound.
-/

public section

open Filter Topology Set MeasureTheory Finset

namespace Zeta5Irrational

/-- The external field of (6.1). -/
@[expose] noncomputable def Vfield (t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt t + (∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2)) -
    6 * ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2)

/-- `w(y) ≤ (1/π) (1 + 2πy)^5 e^{-2πy}` for `y > 0`. -/
lemma w_le' {y : ℝ} (hy : 0 < y) :
    w y ≤ 1 / Real.pi * (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(2 * Real.pi * y)) := by
  rw [w_eq_F4 hy]
  have h := abs_F4_le hy
  have hF : F4 y ≤ 24 * (1 + 2 * Real.pi * y) ^ (4 + 1) / (2 * Real.pi * y ^ (4 + 1) * qe y) :=
    (le_abs_self _).trans h
  have hq : qe y = Real.exp (2 * Real.pi * y) := rfl
  have hqinv : 1 / qe y = Real.exp (-(2 * Real.pi * y)) := by rw [hq, Real.exp_neg, one_div]
  have hqpos := qe_pos y
  calc
    y ^ 5 * F4 y / 12 ≤
        y ^ 5 * (24 * (1 + 2 * Real.pi * y) ^ (4 + 1) / (2 * Real.pi * y ^ (4 + 1) * qe y)) /
          12 :=
      by gcongr
    _ = 1 / Real.pi * (1 + 2 * Real.pi * y) ^ 5 * (1 / qe y) := by
      field_simp
      ring
    _ = _ := by rw [hqinv]

/-- The monotone comparison (6.12): for `t > 0` and `1 ≤ m`,
`K ∫₀^{m/K} log(t+u²) du ≤ ∑_{j=1}^m log(t + (j/K)²)`. -/
lemma integral_le_sum_log {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : 0 < K) (m : ℕ) :
    K * ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log (t + u ^ 2) ≤
      ∑ j ∈ range m, Real.log (t + (((j : ℝ) + 1) / K) ^ 2) := by
  -- substitution `u = v / K` and the monotone comparison on `[0, m]`
  have hmono : MonotoneOn (fun v : ℝ => Real.log (t + (v / K) ^ 2)) (Icc 0 (0 + (m : ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := hx.1
    refine Real.log_le_log (by positivity) ?_
    gcongr
  have hcmp := hmono.integral_le_sum
  simp only [zero_add] at hcmp
        -- change of variables in the integral
  have hsub :
    ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log (t + u ^ 2) =
      (1 / K) * ∫ v in (0 : ℝ)..(m : ℝ), Real.log (t + (v / K) ^ 2) := by
    have :=
      intervalIntegral.integral_comp_div (fun u => Real.log (t + u ^ 2)) (a := 0) (b := (m : ℝ))
        hK.ne'
    simp only [zero_div] at this
    rw [this, smul_eq_mul]; field_simp
  rw [hsub]
  have h1 :
    K * (1 / K * ∫ v in (0 : ℝ)..(m : ℝ), Real.log (t + (v / K) ^ 2)) =
      ∫ v in (0 : ℝ)..(m : ℝ), Real.log (t + (v / K) ^ 2) :=
    by field_simp
  rw [h1]
  refine hcmp.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring_nf

/-- A weakening of the reverse comparison (6.12): for `t > 0`, `1 ≤ m ≤ K`,
`∑_{j=1}^m log(t + (j/K)²) ≤ K ∫₀^{m/K} log(t+u²) du + 2 log(2K) + 2`.
The paper has the sharper remainder `2 log K + 2`. -/
lemma sum_log_le_integral {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    (hmK : (m : ℝ) ≤ K) :
    ∑ j ∈ range m, Real.log (t + (((j : ℝ) + 1) / K) ^ 2) ≤
      K * (∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log (t + u ^ 2)) + 2 * Real.log (2 * K) + 2 := by
  have hK0 : 0 < K := by linarith
  set f : ℝ → ℝ := fun u => Real.log (t + u ^ 2) with hf
  have hfcont : Continuous f := by
    rw [hf];
    exact Continuous.log (by fun_prop) (fun u => by positivity)
  have hfint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    hfcont.intervalIntegrable a b
  set c : ℝ := (m : ℝ) / K with hc
  have hc0 : 0 ≤ c := by
    positivity
      -- (L1) right-endpoint sums vs the shifted integral
  have hmono : MonotoneOn (fun v : ℝ => f ((v + 1) / K)) (Icc 0 (0 + (m : ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := hx.1
    simp only [hf]
    refine Real.log_le_log (by positivity) ?_
    gcongr
  have hcmp := hmono.sum_le_integral
  simp only [zero_add] at hcmp
  have hshift :
    ∫ v in (0 : ℝ)..(m : ℝ), f ((v + 1) / K) = K * ∫ u in (1 / K : ℝ)..(((m : ℝ) + 1) / K), f u :=
  by
    have h1 :=
      intervalIntegral.integral_comp_add_right (fun v => f (v / K)) (a := 0) (b := (m : ℝ)) 1
    have h2 := intervalIntegral.integral_comp_div f (a := 1) (b := (m : ℝ) + 1) hK0.ne'
    simp only [zero_add] at h1
    rw [h1, h2, smul_eq_mul]
      -- (L2) splitting
  have hfint' : IntervalIntegrable (fun u => f (u + c)) volume 0 (1 / K) :=
    (hfcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hsplit :
    ∫ u in (1 / K : ℝ)..(((m : ℝ) + 1) / K), f u =
      (∫ u in (0 : ℝ)..c, f u) + ∫ u in (0 : ℝ)..(1 / K : ℝ), (f (u + c) - f u) := by
    rw [intervalIntegral.integral_sub hfint' (hfint _ _),
      intervalIntegral.integral_comp_add_right f c]
    have e1 :=
      intervalIntegral.integral_add_adjacent_intervals (hfint 0 (1 / K))
        (hfint (1 / K) (((m : ℝ) + 1) / K))
    have e2 :=
      intervalIntegral.integral_add_adjacent_intervals (hfint 0 c) (hfint c (((m : ℝ) + 1) / K))
    have e3 : (0 : ℝ) + c = c := by ring
    have e4 : 1 / K + c = ((m : ℝ) + 1) / K := by rw [hc]; field_simp; ring
    rw [e3, e4]
    linarith
      -- (L3) pointwise bound on `(0, 1/K)`
  have hpt : ∀ u ∈ Ioo (0 : ℝ) (1 / K), f (u + c) - f u ≤ 2 * (Real.log (u + c) - Real.log u) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    simp only [hf]
    rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div (by positivity) hu0.ne',
      show (2 : ℝ) * Real.log ((u + c) / u) = Real.log (((u + c) / u) ^ 2) by
        rw [Real.log_pow];
        push_cast; ring]
    refine Real.log_le_log (by positivity) ?_
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u,
      mul_nonneg ht.le (mul_nonneg hc0 (by positivity : (0 : ℝ) ≤ 2 * u + c))]
      -- (L4) the two logarithmic integrals
  have hI1 : ∫ u in (0 : ℝ)..(1 / K : ℝ), Real.log u = 1 / K * Real.log (1 / K) - 1 / K := by
    rw [integral_log]; simp
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcpos : 0 < c := by rw [hc]; exact div_pos (by linarith) hK0
  have hcont2 : IntervalIntegrable (fun u => Real.log (u + c)) volume 0 (1 / K) := by
    refine ContinuousOn.intervalIntegrable (ContinuousOn.log (by fun_prop) (fun u hu => ?_))
    rw [Set.uIcc_of_le (by positivity)] at hu
    have := hu.1
    exact (by linarith : (0 : ℝ) < u + c).ne'
  have hI2 :
    ∫ u in (0 : ℝ)..(1 / K : ℝ), Real.log (u + c) ≤ 1 / K * Real.log (((m : ℝ) + 1) / K) := by
    have hle : ∀ u ∈ Icc (0 : ℝ) (1 / K), Real.log (u + c) ≤ Real.log (((m : ℝ) + 1) / K) := by
      intro u hu
      refine Real.log_le_log (by linarith [hu.1]) ?_
      have e : ((m : ℝ) + 1) / K = 1 / K + c := by rw [hc]; field_simp; ring
      rw [e]; linarith [hu.2]
    have := intervalIntegral.integral_mono_on (by positivity) hcont2 intervalIntegrable_const hle
    simpa [intervalIntegral.integral_const] using this
  have hlogint : IntervalIntegrable Real.log volume 0 (1 / K) :=
    intervalIntegral.intervalIntegrable_log'
  have hdiff :
    ∫ u in (0 : ℝ)..(1 / K : ℝ), (f (u + c) - f u) ≤
      2 *
        ((∫ u in (0 : ℝ)..(1 / K : ℝ), Real.log (u + c)) -
          ∫ u in (0 : ℝ)..(1 / K : ℝ), Real.log u) := by
    rw [← intervalIntegral.integral_sub hcont2 hlogint, ← intervalIntegral.integral_const_mul]
    exact
      intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) (hfint'.sub (hfint _ _))
        ((hcont2.sub hlogint).const_mul 2)
        hpt
          -- combine
  have hlog2 : Real.log (((m : ℝ) + 1) / K) - Real.log (1 / K) ≤ Real.log (2 * K) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    have e : ((m : ℝ) + 1) / K / (1 / K) = (m : ℝ) + 1 := by field_simp
    rw [e]; linarith
  calc
    ∑ x ∈ range m, f ((↑x + 1) / K) ≤ ∫ v in (0 : ℝ)..(m : ℝ), f ((v + 1) / K) := hcmp
    _ = K * ((∫ u in (0 : ℝ)..c, f u) + ∫ u in (0 : ℝ)..(1 / K : ℝ), (f (u + c) - f u)) := by
      rw [hshift, hsplit]
    _ ≤
        K *
          ((∫ u in (0 : ℝ)..c, f u) +
            2 * ((1 / K * Real.log (((m : ℝ) + 1) / K)) - (1 / K * Real.log (1 / K) - 1 / K))) := by
      gcongr
      rw [← hI1]
      exact hdiff.trans (by gcongr)
    _ =
        K * (∫ u in (0 : ℝ)..c, f u) + 2 * (Real.log (((m : ℝ) + 1) / K) - Real.log (1 / K)) +
          2 := by
      field_simp
      ring
    _ ≤ K * (∫ u in (0 : ℝ)..c, f u) + 2 * Real.log (2 * K) + 2 := by gcongr

/-- `∫₀^∞ (1 + 2πy)^5 e^{-y/K} dy ≤ (2π)^5 · 32 · 121 · K^6` for `K ≥ 1`. -/
lemma integral_one_add_pow_mul_exp {K : ℝ} (hK : 1 ≤ K) :
    ∫ y in Ioi 0, (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / K * y)) ≤
      (2 * Real.pi) ^ 5 * 32 * 121 * K ^ 6 := by
  have hK0 : 0 < K := by linarith
  have hr : 0 < 1 / K := by positivity
  have hpi :=
    Real.pi_gt_three
      -- the dominating function
  have hg :
    IntegrableOn
      (fun y : ℝ =>
        (2 * Real.pi) ^ 5 * 32 * (y ^ 0 * Real.exp (-(1 / K * y))) +
          (2 * Real.pi) ^ 5 * 32 * (y ^ 5 * Real.exp (-(1 / K * y))))
      (Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul 0 hr).const_mul _).add
      ((integrableOn_pow_mul_exp_neg_mul 5 hr).const_mul _)
  have hle :
    ∀ y : ℝ,
      0 < y →
        (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / K * y)) ≤
          (2 * Real.pi) ^ 5 * 32 * (y ^ 0 * Real.exp (-(1 / K * y))) +
            (2 * Real.pi) ^ 5 * 32 * (y ^ 5 * Real.exp (-(1 / K * y))) := by
    intro y hy
    have h1 : (1 + 2 * Real.pi * y) ^ 5 ≤ (2 * Real.pi) ^ 5 * (1 + y) ^ 5 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) 5
    have h2 : (1 + y) ^ 5 ≤ 32 * (1 + y ^ 5) := by
      rcases le_or_gt y 1 with h | h
      · have : (1 + y) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        have : 0 ≤ y ^ 5 := by positivity
        nlinarith
      · have : (1 + y) ^ 5 ≤ (2 * y) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        have : 0 ≤ y ^ 5 := by positivity
        nlinarith
    have he : 0 ≤ Real.exp (-(1 / K * y)) := (Real.exp_pos _).le
    calc
      (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / K * y)) ≤
          (2 * Real.pi) ^ 5 * (32 * (1 + y ^ 5)) * Real.exp (-(1 / K * y)) := by
        gcongr
        exact h1.trans (by gcongr)
      _ = _ := by simp only [pow_zero, one_mul]; ring
  have hnn :
    0 ≤ᵐ[volume.restrict (Ioi 0)] fun y : ℝ =>
      (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / K * y)) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy =>
        by
        have : (0 : ℝ) < y := hy
        positivity)
  have hmono :
    ∀ᵐ y ∂(volume.restrict (Ioi 0)),
      (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / K * y)) ≤
        (2 * Real.pi) ^ 5 * 32 * (y ^ 0 * Real.exp (-(1 / K * y))) +
          (2 * Real.pi) ^ 5 * 32 * (y ^ 5 * Real.exp (-(1 / K * y))) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => hle y hy)
  calc
    ∫ y in Ioi 0, (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / K * y)) ≤
        ∫ y in Ioi 0,
          ((2 * Real.pi) ^ 5 * 32 * (y ^ 0 * Real.exp (-(1 / K * y))) +
            (2 * Real.pi) ^ 5 * 32 * (y ^ 5 * Real.exp (-(1 / K * y)))) :=
      integral_mono_of_nonneg hnn hg hmono
    _ =
        (2 * Real.pi) ^ 5 * 32 * ((0 : ℕ).factorial / (1 / K) ^ (0 + 1)) +
          (2 * Real.pi) ^ 5 * 32 * ((5 : ℕ).factorial / (1 / K) ^ (5 + 1)) := by
      rw [integral_add ((integrableOn_pow_mul_exp_neg_mul 0 hr).const_mul _)
          ((integrableOn_pow_mul_exp_neg_mul 5 hr).const_mul _),
        integral_const_mul, integral_const_mul, integral_pow_mul_exp_neg_mul 0 hr,
        integral_pow_mul_exp_neg_mul 5 hr]
    _ = (2 * Real.pi) ^ 5 * 32 * (K + 120 * K ^ 6) := by
      simp only [Nat.factorial]; norm_num
      all_goals field_simp
    _ ≤ (2 * Real.pi) ^ 5 * 32 * 121 * K ^ 6 := by
      have : K ≤ K ^ 6 := by
        calc
          K = K ^ 1 := (pow_one K).symm
          _ ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
      nlinarith [pow_pos (by positivity : (0 : ℝ) < 2 * Real.pi) 5]

/-! ### Almost every configuration has positive, pairwise distinct coordinates -/

/-- The hyperplane `{x | x i = x j}` is null for Lebesgue measure on `Fin h → ℝ`. -/
lemma volume_eq_coord_null {h : ℕ} {i j : Fin h} (hij : i ≠ j) :
    (volume : Measure (Fin h → ℝ)) {x | x i = x j} = 0 := by
  set L : (Fin h → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin h => ℝ) i -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin h => ℝ) j with
    hL
  have hset : {x : Fin h → ℝ | x i = x j} = (LinearMap.ker L : Set (Fin h → ℝ)) := by
    ext x
    simp [hL, LinearMap.mem_ker, sub_eq_zero]
  rw [hset]
  refine Measure.addHaar_submodule volume _ ?_
  intro htop
  have hmem : (Pi.single i (1 : ℝ) : Fin h → ℝ) ∈ LinearMap.ker L := by
    rw [htop];
    exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hmem
  simp [hL, hij.symm] at hmem

/-- Almost every `x` (for `dy` on `(0,∞)^h`) has positive, pairwise distinct coordinates. -/
lemma ae_pos_injective (h : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin h => μpos), (∀ i, 0 < x i) ∧ Function.Injective x := by
  have hpi :
    (Measure.pi fun _ : Fin h => μpos) =
      (volume : Measure (Fin h → ℝ)).restrict (Set.pi univ fun _ => Ioi 0) :=
    by rw [volume_pi, Measure.restrict_pi_pi]
  rw [hpi]
  have h1 :
    ∀ᵐ x ∂((volume : Measure (Fin h → ℝ)).restrict (Set.pi univ fun _ => Ioi 0)), ∀ i, 0 < x i := by
    have :=
      ae_restrict_mem (μ := (volume : Measure (Fin h → ℝ))) (s :=
        Set.pi univ fun _ : Fin h => Ioi (0 : ℝ))
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)
    filter_upwards [this] with x hx
    intro i
    exact hx i (Set.mem_univ i)
  have hac : (volume : Measure (Fin h → ℝ)).restrict (Set.pi univ fun _ => Ioi 0) ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have h2 :
    ∀ᵐ x ∂((volume : Measure (Fin h → ℝ)).restrict (Set.pi univ fun _ => Ioi 0)),
      Function.Injective x := by
    have hall :
      ∀ᵐ x ∂((volume : Measure (Fin h → ℝ)).restrict (Set.pi univ fun _ => Ioi 0)),
        ∀ i j, i ≠ j → x i ≠ x j := by
      rw [ae_all_iff]; intro i
      rw [ae_all_iff]; intro j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun x h => absurd hij h
      · have h0 : (volume : Measure (Fin h → ℝ)) {x | x i = x j} = 0 := volume_eq_coord_null hij
        have h1 := hac h0
        rw [ae_iff]
        convert h1 using 2
        ext x; simp [hij]
    filter_upwards [hall] with x hx
    intro i j hxy
    by_contra hij
    exact hx i j hij hxy
  exact h1.and h2

end Zeta5Irrational
