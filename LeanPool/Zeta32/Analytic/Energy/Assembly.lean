/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Potential
public import LeanPool.Zeta32.Analytic.Energy.Scaling
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Real.Pi.Bounds

/-! the proof notes (11′), (14′), (15′): tail margin, integration of the configuration bound,
and the constant `F* = 9(3/2 − log 3) + (9/2)(ℓ − W) ≤ −6`. -/

public section

open Real MeasureTheory Polynomial Filter Topology

namespace Zeta32.Analytic.EnergyI
noncomputable section

theorem Wt_lower {y : ℝ} (hy : 0 ≤ y) : (2/3) * (π * y - 2 - Real.log (1 + y^2)) ≤ Wt y := by
  rcases hy.lt_or_eq with hy | hy
  · have h1 : y * Real.arctan (1/y) ≤ 1 := by
      have := Real.arctan_le_self (show (0:ℝ) ≤ 1/y by positivity)
      calc y * Real.arctan (1/y) ≤ y * (1/y) := mul_le_mul_of_nonneg_left this hy.le
        _ = 1 := by field_simp
    have h2 : 0 ≤ y * Real.arctan (5/y) :=
      mul_nonneg hy.le (Real.arctan_nonneg.mpr (by positivity))
    have h3 : 0 ≤ Real.log (1 + y^2/25) := Real.log_nonneg (by nlinarith [sq_nonneg y])
    unfold Wt
    nlinarith
  · subst hy
    have : (2/3) * (π * 0 - 2 - Real.log (1 + 0^2)) = (-4/3 : ℝ) := by simp; norm_num
    rw [this]; unfold Wt; simp; norm_num

/-- (11′): the margin `2L − W ≤ ℓ − max(0, |x| − B)`. -/
theorem tail_bound {a : ℝ} (ha : 0 < a) (hm : massA a = 1) :
    ∃ B : ℝ, ∀ x : ℝ, 2 * potA a x - Wt |x| ≤ ellA a - max 0 (|x| - B) := by
  refine ⟨|ellA a| + a + 10, fun x => ?_⟩
  have h1 := potA_le ha hm x
  rcases le_total (|x| - (|ellA a| + a + 10)) 0 with hx | hx
  · rw [max_eq_left hx]; linarith
  rw [max_eq_right hx]
  have h2 := potA_le_log ha hm x
  have h3 := Wt_lower (abs_nonneg x)
  have hx0 := abs_nonneg x
  have hl1 : Real.log (|x| + a) ≤ Real.log 8 + (|x| + a) / 8 - 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < (|x| + a) / 8 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at this
    linarith
  have hl2 : Real.log (1 + |x|^2) ≤ 2 * (Real.log 8 + (1 + |x|) / 8 - 1) := by
    have e : Real.log (1 + |x|^2) ≤ Real.log ((1 + |x|)^2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at e
    have := Real.log_le_sub_one_of_pos (show 0 < (1 + |x|) / 8 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at this
    push_cast at e
    linarith
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
  have hlog2 := Real.log_two_lt_d9
  have hpi := Real.pi_gt_three
  have habs := le_abs_self (ellA a)
  have habs' := neg_abs_le (ellA a)
  rw [sq_abs] at hl2
  have hpix : 3 * |x| ≤ π * |x| := mul_le_mul_of_nonneg_right hpi.le hx0
  rw [sq_abs] at h3
  linarith

theorem filter_lt_eq_Ioi {m : ℕ} (l : Fin m) :
    Finset.univ.filter (fun l' => l < l') = Finset.Ioi l := by
  ext; simp

theorem vandermonde_eq_exp {m : ℕ} (x : Fin m → ℝ) (hx : Function.Injective x) :
    ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2 =
      Real.exp (2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [filter_lt_eq_Ioi, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun l' hl' => ?_
  have hne : x l' - x l ≠ 0 :=
    sub_ne_zero.mpr fun h => (ne_of_lt (Finset.mem_Ioi.mp hl')).symm (hx h)
  rw [show 2 * Real.log |x l' - x l| = Real.log (|x l' - x l|^2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity), sq_abs]
  ring

theorem vandermonde_eq_zero {m : ℕ} (x : Fin m → ℝ) (hx : ¬ Function.Injective x) :
    ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2 = 0 := by
  simp only [Function.Injective, not_forall] at hx
  obtain ⟨i, j, hij, hne⟩ := hx
  rcases lt_or_gt_of_ne hne with h | h
  · exact Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (by simpa using h) (by rw [hij]; ring))
  · exact Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (by simpa using h) (by rw [hij]; ring))

/-- Configuration bound: (13′) with `ε = (n+1)⁻²`, combined with `2L − W ≤ ℓ − max(0, |x| − B)`. -/
theorem config_bound {a : ℝ} (ha : 0 < a) (hm : massA a = 1) : ∃ B C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∀ x : Fin (3*n) → ℝ,
      (∏ l, Real.exp (-(3 * (n:ℝ)) * Wt |x l|)) *
          ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2 ≤
        Real.exp (9 * (n:ℝ)^2 * (ellA a - IA a) + C * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1)) *
          ∏ l, Real.exp (-(3 * (n:ℝ)) * max 0 (|x l| - B)) := by
  obtain ⟨B, hB⟩ := tail_bound ha hm
  have hρ := rhoA_good ha hm
  set N2 := ∫ t in (-a)..a, rhoA a t ^ 2 with hN2def
  have hN2 : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  set K0 := 32 + N2 / 2 with hK0def
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨B, 6 + 18 * K0, fun n hn x => ?_⟩
  have hn0 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hRHS : 0 < Real.exp (9 * (n:ℝ)^2 * (ellA a - IA a) + (6 + 18 * K0) * (n:ℝ) *
      (Real.log ((n:ℝ) + 1) + 1)) * ∏ l, Real.exp (-(3 * (n:ℝ)) * max 0 (|x l| - B)) :=
    mul_pos (Real.exp_pos _) (Finset.prod_pos fun _ _ => Real.exp_pos _)
  by_cases hinj : Function.Injective x
  swap
  · rw [vandermonde_eq_zero x hinj, mul_zero]; exact hRHS.le
  set ε : ℝ := 1 / ((n:ℝ) + 1)^2 with hεdef
  have hε : 0 < ε := by positivity
  have hsq : √ε = 1 / ((n:ℝ) + 1) := by
    rw [hεdef, Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq (by positivity)]
  have hlogε : Real.log ε = -(2 * Real.log ((n:ℝ) + 1)) := by
    rw [hεdef, one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  have hD := discrete_energy hρ (h := 3*n) (by omega) x hinj hε
  change _ ≤ 2 * ((3*n : ℕ) : ℝ) * ∑ i, potA a (x i) - ((3*n : ℕ) : ℝ)^2 * IA a -
    ((3*n : ℕ) : ℝ) * Real.log ε + 2 * ((3*n : ℕ) : ℝ)^2 * (√ε * K0) at hD
  push_cast at hD
  rw [vandermonde_eq_exp x hinj, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hpot : ∀ i, 2 * potA a (x i) ≤ ellA a + Wt |x i| - max 0 (|x i| - B) :=
    fun i => by linarith [hB (x i)]
  have hsum : 2 * ∑ i, potA a (x i) ≤
      3 * (n:ℝ) * ellA a + ∑ i, Wt |x i| - ∑ i, max 0 (|x i| - B) := by
    rw [Finset.mul_sum]
    calc ∑ i, 2 * potA a (x i) ≤ ∑ i : Fin (3*n), (ellA a + Wt |x i| - max 0 (|x i| - B)) :=
          Finset.sum_le_sum fun i _ => hpot i
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hsW : ∑ l, -(3 * (n:ℝ)) * Wt |x l| = -(3 * (n:ℝ)) * ∑ l, Wt |x l| := by
    rw [Finset.mul_sum]
  have hsM : ∑ l, -(3 * (n:ℝ)) * max 0 (|x l| - B) = -(3 * (n:ℝ)) * ∑ l, max 0 (|x l| - B) := by
    rw [Finset.mul_sum]
  rw [hsW, hsM]
  rw [hsq, hlogε] at hD
  have hlog1 : 0 ≤ Real.log ((n:ℝ) + 1) := Real.log_nonneg (by linarith)
  have herr : 2 * (3 * (n:ℝ))^2 * (1 / ((n:ℝ) + 1) * K0) ≤ 18 * K0 * n := by
    rw [show 2 * (3 * (n:ℝ))^2 * (1 / ((n:ℝ) + 1) * K0) = 18 * K0 * n * (n / (n + 1)) by
      field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  have h3n : (0:ℝ) ≤ 3 * n := by positivity
  have key := mul_le_mul_of_nonneg_left hsum h3n
  nlinarith [mul_nonneg hK0 (mul_nonneg (by positivity : (0:ℝ) ≤ n) hlog1)]

/-- The tail integrand. -/
def tailFun (B m : ℝ) (y : ℝ) : ℝ := (1 + |y|)^7 * Real.exp (-m * max 0 (|y| - B))

theorem continuous_tailFun (B m : ℝ) : Continuous (tailFun B m) := by
  unfold tailFun; fun_prop

theorem tailFun_le_one_add_sq (B : ℝ) {m : ℝ} (hm : 1 ≤ m) (y : ℝ) :
    tailFun B m y ≤ (Real.exp B * (Nat.factorial 9 * Real.exp 1)) * (1 + y^2)⁻¹ := by
  unfold tailFun
  have hy := abs_nonneg y
  have h1 : Real.exp (-m * max 0 (|y| - B)) ≤ Real.exp B * Real.exp (-|y|) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := le_max_right 0 (|y| - B)
    have h0 := le_max_left 0 (|y| - B)
    nlinarith
  have h2 : (1 + |y|)^9 ≤ Nat.factorial 9 * Real.exp (1 + |y|) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + |y|) (by positivity) 9
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have h3 : (1 + y^2) ≤ (1 + |y|)^2 := by nlinarith [sq_abs y]
  have hpos : 0 < 1 + y^2 := by positivity
  rw [le_mul_inv_iff₀ hpos]
  calc (1 + |y|)^7 * Real.exp (-m * max 0 (|y| - B)) * (1 + y^2)
      ≤ (1 + |y|)^7 * (Real.exp B * Real.exp (-|y|)) * (1 + |y|)^2 := by gcongr
    _ = Real.exp B * (1 + |y|)^9 * Real.exp (-|y|) := by ring
    _ ≤ Real.exp B * (Nat.factorial 9 * Real.exp (1 + |y|)) * Real.exp (-|y|) := by gcongr
    _ = Real.exp B * (Nat.factorial 9 * Real.exp 1) := by
      rw [Real.exp_add]
      have : Real.exp |y| * Real.exp (-|y|) = 1 := by rw [← Real.exp_add]; simp
      linear_combination (Real.exp B * (Nat.factorial 9 * Real.exp 1)) * this

theorem integrable_tailFun (B : ℝ) {m : ℝ} (hm : 1 ≤ m) : Integrable (tailFun B m) := by
  refine (integrable_inv_one_add_sq.const_mul (Real.exp B * (Nat.factorial 9 * Real.exp 1))).mono'
    (continuous_tailFun B m).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold tailFun; positivity)]
  exact tailFun_le_one_add_sq B hm y

theorem integral_tailFun_le (B : ℝ) {m : ℝ} (hm : 1 ≤ m) :
    ∫ y, tailFun B m y ≤ ∫ y, tailFun B 1 y := by
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by unfold tailFun; positivity)
    (integrable_tailFun B le_rfl)
  refine Filter.Eventually.of_forall fun y => ?_
  unfold tailFun
  gcongr

theorem eventually_lin_log_le (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, M * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) ≤ δ * (n:ℝ)^2 := by
  -- adapted from Li2Unified/Modular/Positive/Packed/P104.lean (star_n_log_eventually_le_square)
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using!
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hshift
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hK : Tendsto (fun n : ℕ => |M| * (Real.log ((n : ℝ) + 1) / (n : ℝ) + 1 / (n:ℝ)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using! (hlog.add hinv).const_mul |M|
  filter_upwards [hK.eventually_le_const hδ, eventually_ge_atTop (1 : ℕ)] with n hnerr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : 0 ≤ Real.log ((n:ℝ) + 1) := Real.log_nonneg (by linarith)
  have hl : |M| * (Real.log ((n : ℝ) + 1) + 1) ≤ δ * n := by
    have e : |M| * (Real.log ((n : ℝ) + 1) / (n : ℝ) + 1 / (n:ℝ)) =
        |M| * (Real.log ((n : ℝ) + 1) + 1) / n := by field_simp
    rw [e, div_le_iff₀ hnpos] at hnerr; exact hnerr
  calc M * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) ≤ |M| * (Real.log ((n : ℝ) + 1) + 1) * n := by
        rw [mul_right_comm]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self M)
          (by linarith)) hnpos.le
    _ ≤ δ * n * n := mul_le_mul_of_nonneg_right hl hnpos.le
    _ = δ * (n:ℝ)^2 := by ring

/-- The energy bound in exponential form (unlike a logarithmic form, it does not need `Q ≠ 0`). -/
theorem energy_bound_exp (r : ℚ) (hH : ∀ n, HeineBound r n) (hF : FstarInput) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |aeval (Cr r) (Qtilde r n)| ≤ Real.exp ((-6 + ε) * (n:ℝ)^2) := by
  obtain ⟨a, ha, hm⟩ := exists_massA_eq_one
  have hFa := hF a ha hm
  have hI := IA_eq ha hm
  have hconst : 9 * (3/2 - Real.log 3) + 9 * (ellA a - IA a) ≤ -6 := by linarith
  obtain ⟨C1, hC1⟩ := heine_scaled r
  obtain ⟨B, C2, hC2⟩ := config_bound ha hm
  set K := max 1 (∫ y, tailFun B 1 y) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  filter_upwards [eventually_lin_log_le (|C1| + |C2| + 3 * Real.log K) hε,
    eventually_ge_atTop 1] with n hlin hn
  have hn0 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 0 ≤ Real.log ((n:ℝ) + 1) := Real.log_nonneg (by linarith)
  set E := 9 * (n:ℝ)^2 * (ellA a - IA a) + C2 * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) with hE
  have hm3 : (1:ℝ) ≤ 3 * (n:ℝ) := by linarith
  -- pointwise domination of the scaled Heine integrand
  have hdom : ∀ x : Fin (3*n) → ℝ,
      (∏ l, ((1 + |x l|)^7 * Real.exp (-(3 * (n:ℝ)) * Wt |x l|))) *
          ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2 ≤
        Real.exp E * ∏ l, tailFun B (3 * (n:ℝ)) (x l) := by
    intro x
    have h := hC2 n hn x
    rw [Finset.prod_mul_distrib, mul_assoc]
    unfold tailFun
    rw [Finset.prod_mul_distrib]
    calc (∏ l, (1 + |x l|)^7) * ((∏ l, Real.exp (-(3 * (n:ℝ)) * Wt |x l|)) *
          ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l')^2)
        ≤ (∏ l, (1 + |x l|)^7) * (Real.exp E *
          ∏ l, Real.exp (-(3 * (n:ℝ)) * max 0 (|x l| - B))) :=
          mul_le_mul_of_nonneg_left h (Finset.prod_nonneg fun _ _ => by positivity)
      _ = _ := by ring
  have hint : Integrable (fun x : Fin (3*n) → ℝ => Real.exp E * ∏ l, tailFun B (3 * (n:ℝ)) (x l)) :=
    (Integrable.fintype_prod (f := fun _ => tailFun B (3 * (n:ℝ)))
      (fun _ => integrable_tailFun B hm3)).const_mul _
  have hInt : ∫ x : Fin (3*n) → ℝ, Real.exp E * ∏ l, tailFun B (3 * (n:ℝ)) (x l) ≤
      Real.exp E * K ^ (3*n) := by
    rw [integral_const_mul, integral_fintype_prod_volume_eq_pow, Fintype.card_fin]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply pow_le_pow_left₀ (integral_nonneg fun y => by unfold tailFun; positivity)
    exact (integral_tailFun_le B hm3).trans (le_max_right _ _)
  have hKpow : K ^ (3*n) = Real.exp (3 * (n:ℝ) * Real.log K) := by
    rw [← Real.exp_log (by linarith : (0:ℝ) < K), ← Real.exp_nat_mul, Real.exp_log (by linarith)]
    push_cast; ring_nf
  refine (hC1 n hn (hH n) _ hint hdom).trans ?_
  refine (mul_le_mul_of_nonneg_left hInt (Real.exp_pos _).le).trans ?_
  rw [hKpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hA1 : C1 * (n:ℝ) * Real.log ((n:ℝ) + 1) ≤ |C1| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C1)
      (mul_nonneg (by positivity : (0:ℝ) ≤ n) hlog1), abs_nonneg C1]
  have hA2 : C2 * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) ≤
      |C2| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity))
      (by positivity)
  have hA3 : 3 * (n:ℝ) * Real.log K ≤ 3 * Real.log K * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) := by
    nlinarith [mul_nonneg (mul_nonneg hlogK (by positivity : (0:ℝ) ≤ n)) hlog1]
  have hsplit : (|C1| + |C2| + 3 * Real.log K) * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) =
      |C1| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) + |C2| * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) +
        3 * Real.log K * (n:ℝ) * (Real.log ((n:ℝ) + 1) + 1) := by ring
  have hc2 := mul_le_mul_of_nonneg_right hconst (sq_nonneg (n:ℝ))
  nlinarith

end
end Zeta32.Analytic.EnergyI

end
