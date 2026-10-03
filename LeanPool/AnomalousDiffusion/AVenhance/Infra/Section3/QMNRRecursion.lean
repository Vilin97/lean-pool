/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.JMNPeriodAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.QMNR
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Regularity and period primitives for the explicit `qMNR` recursion. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.Infra.Section3

open AVenhance

theorem QMNRRecursion.matrixEntry_continuous {f : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hf : Continuous f) (i j : Fin 2) : Continuous (fun t => f t i j) := by
  have heval : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  exact heval.comp hf

/-- Every entry in the recursively defined family is continuous. -/
theorem qMNR_entry_continuous {β : ℝ} (I : Ingredients β) (κ : ℝ)
    (m n r : ℕ) (i j : Fin 2) : Continuous (fun t => I.qMNR κ m n r t i j) := by
  induction r with
  | zero =>
      simp only [Ingredients.qMNR]
      exact (QMNRRecursion.matrixEntry_continuous (jMN_continuous I m n κ) i j).sub continuous_const
  | succ r ih =>
      let f : ℝ → ℝ := fun t => I.qMNR κ m n r t i j
      have hf : Continuous f := ih
      have hprimitive : Continuous (fun t => ∫ s in (0 : ℝ)..t, f s) :=
        intervalIntegral.continuous_primitive
          (fun a b => hf.intervalIntegrable a b) 0
      let c : ℝ := timeAvgMat (fun u => Matrix.of fun i j =>
        ∫ s in (0 : ℝ)..u, I.qMNR κ m n r s i j) i j
      change Continuous (fun t => -(∫ s in (0 : ℝ)..t, f s) + c)
      exact hprimitive.neg.add continuous_const

/-- Every positive recursion level has zero unit-time average by construction. -/
theorem qMNR_timeAvg_zero {β : ℝ} (I : Ingredients β) (κ : ℝ)
    (m n r : ℕ) : timeAvgMat (I.qMNR κ m n (r + 1)) = 0 := by
  ext i j
  let f : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, I.qMNR κ m n r s i j
  have hf : Continuous f := by
    have hentry := qMNR_entry_continuous I κ m n r i j
    exact intervalIntegral.continuous_primitive
      (fun a b => hentry.intervalIntegrable a b) 0
  have hint : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable 0 1
  let c : ℝ := timeAvgMat (fun u => Matrix.of fun i j =>
    ∫ s in (0 : ℝ)..u, I.qMNR κ m n r s i j) i j
  have hconst : c = ∫ t in (0 : ℝ)..1, f t := rfl
  change (∫ t in (0 : ℝ)..1,
      I.qMNR κ m n (r + 1) t i j) = 0
  change (∫ t in (0 : ℝ)..1, (-f t + c)) = 0
  have hpoint : (fun t : ℝ => -f t + c) = fun t => c - f t := by
    funext t
    ring
  rw [hpoint, intervalIntegral.integral_sub
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 1) hint]
  simp [hconst]

theorem QMNRRecursion.period_integral_zero_of_unit_average_zero {f : ℝ → ℝ}
    {P : ℝ} {N : ℕ} (hperiodic : Function.Periodic f P)
    (hcont : Continuous f) (hunit : (N : ℝ) * P = 1)
    (havg : (∫ t in (0 : ℝ)..1, f t) = 0) :
    (∫ t in (0 : ℝ)..P, f t) = 0 := by
  have hmul := intervalIntegral_unit_eq_period_mul hperiodic hcont hunit
  rw [havg] at hmul
  have hN : (N : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    norm_num at hunit
  have hprod : (N : ℝ) * (∫ t in (0 : ℝ)..P, f t) = 0 := by
    linarith
  exact (mul_eq_zero.mp hprod).resolve_left hN

/-- Every recursively defined `qMNR` level is periodic, and has zero mean on
one `4τ_m` cell. The base case uses the exact integer period count. -/
theorem qMNR_periodic_and_period_mean_zero {β : ℝ} (I : Ingredients β)
    (κ : ℝ) {m n : ℕ} (hm : 1 ≤ m) :
    ∀ r : ℕ,
      Function.Periodic (I.qMNR κ m n r) (4 * tau β I.Λ m) ∧
        ∀ i j : Fin 2,
          (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), I.qMNR κ m n r t i j) = 0 := by
  have hP : 0 < 4 * tau β I.Λ m :=
    mul_pos (by norm_num) (Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)
  obtain ⟨N, hN⟩ := four_tau_reciprocal_nat I hm
  intro r
  induction r with
  | zero =>
      constructor
      · intro t
        simp only [Ingredients.qMNR]
        rw [jMN_period_four_tau I (m := m) κ n t]
      · intro i j
        let f : ℝ → ℝ := fun t => I.jMN κ m n t i j
        have hf : Continuous f := by
          have heval : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) :=
            (continuous_apply j).comp (continuous_apply i)
          exact heval.comp (jMN_continuous I m n κ)
        have hconst : timeAvgMat (I.jMN κ m n) i j =
            (4 * tau β I.Λ m)⁻¹ *
              (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), f t) := by
          simpa [timeAvgMat, f] using jMN_average_eq_period_average I hm κ i j
        have hint : IntervalIntegrable f volume 0 (4 * tau β I.Λ m) :=
          hf.intervalIntegrable 0 _
        change (∫ t in (0 : ℝ)..(4 * tau β I.Λ m),
            f t - timeAvgMat (I.jMN κ m n) i j) = 0
        rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
          intervalIntegral.integral_const]
        rw [hconst]
        have hPne : 4 * tau β I.Λ m ≠ 0 := ne_of_gt hP
        simp only [sub_zero, smul_eq_mul]
        field_simp [hPne]
        simp [ne_of_gt (Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le)]
  | succ r ih =>
      have hsuccPeriodic : Function.Periodic
          (I.qMNR κ m n (r + 1)) (4 * tau β I.Λ m) := by
        intro t
        ext i j
        let f : ℝ → ℝ := fun s => I.qMNR κ m n r s i j
        have hfper : Function.Periodic f (4 * tau β I.Λ m) := by
          intro s
          exact congrFun (congrFun (ih.1 s) i) j
        have hfcont : Continuous f := qMNR_entry_continuous I κ m n r i j
        have hshift :
            (∫ s in (0 : ℝ)..(t + 4 * tau β I.Λ m), f s) =
              ∫ s in (0 : ℝ)..t, f s := by
          have hcell := hfper.intervalIntegral_add_eq t 0
          have hcellzero : (∫ s in t..t + 4 * tau β I.Λ m, f s) = 0 := by
            calc
              (∫ s in t..t + 4 * tau β I.Λ m, f s) =
                  ∫ s in (0 : ℝ)..(4 * tau β I.Λ m), f s := by
                simpa using hcell
              _ = 0 := ih.2 i j
          calc
            (∫ s in (0 : ℝ)..(t + 4 * tau β I.Λ m), f s) =
                (∫ s in (0 : ℝ)..t, f s) +
                  (∫ s in t..t + 4 * tau β I.Λ m, f s) := by
              symm
              exact intervalIntegral.integral_add_adjacent_intervals
                (hfcont.intervalIntegrable 0 t)
                (hfcont.intervalIntegrable t (t + 4 * tau β I.Λ m))
            _ = ∫ s in (0 : ℝ)..t, f s := by rw [hcellzero]; ring
        change -(∫ s in (0 : ℝ)..(t + 4 * tau β I.Λ m), f s) + _ =
          -(∫ s in (0 : ℝ)..t, f s) + _
        rw [hshift]
      constructor
      · exact hsuccPeriodic
      · intro i j
        have hperiod : Function.Periodic
            (fun t => I.qMNR κ m n (r + 1) t i j) (4 * tau β I.Λ m) :=
          fun t => congrFun (congrFun (hsuccPeriodic t) i) j
        have hcont := qMNR_entry_continuous I κ m n (r + 1) i j
        have havg : (∫ t in (0 : ℝ)..1, I.qMNR κ m n (r + 1) t i j) = 0 := by
          have hz := qMNR_timeAvg_zero I κ m n r
          have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hz
          simpa [timeAvgMat] using hentry
        exact QMNRRecursion.period_integral_zero_of_unit_average_zero hperiod hcont hN havg

/-- all recursively constructed `q_{m,n,r}` use the corrected `4τ_m` period. -/
theorem qMNR_periodic {β : ℝ} (I : Ingredients β) (κ : ℝ)
    {m n : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    Function.Periodic (I.qMNR κ m n r) (4 * tau β I.Λ m) :=
  (qMNR_periodic_and_period_mean_zero I κ hm r).1

/-- The defining primitive step satisfies the derivative recursion. -/
theorem qMNR_hasDerivAt {β : ℝ} (I : Ingredients β) (κ : ℝ)
    (m n r : ℕ) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => I.qMNR κ m n (r + 1) s i j)
      (-(I.qMNR κ m n r t i j)) t := by
  let f : ℝ → ℝ := fun s => I.qMNR κ m n r s i j
  have hf : Continuous f := qMNR_entry_continuous I κ m n r i j
  let c : ℝ := timeAvgMat (fun u => Matrix.of fun i j =>
    ∫ s in (0 : ℝ)..u, I.qMNR κ m n r s i j) i j
  have hfun : (fun s => I.qMNR κ m n (r + 1) s i j) =
      fun s => c - ∫ u in (0 : ℝ)..s, f u := by
    funext s
    simp [Ingredients.qMNR, c, f]
    ring
  rw [hfun]
  simpa [f] using (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.const_sub c

theorem QMNRRecursion.eq_of_same_derivative_and_zero_average
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hderivF : ∀ t, HasDerivAt f (deriv f t) t)
    (hderivG : ∀ t, HasDerivAt g (deriv g t) t)
    (hsame : ∀ t, deriv f t = deriv g t)
    (hzeroF : (∫ t in (0 : ℝ)..1, f t) = 0)
    (hzeroG : (∫ t in (0 : ℝ)..1, g t) = 0) : f = g := by
  let d : ℝ → ℝ := f - g
  have hd : ∀ t, HasDerivAt d 0 t := by
    intro t
    have hfg := (hderivF t).sub (hderivG t)
    rw [hsame t] at hfg
    change HasDerivAt d 0 t
    simpa [d] using hfg
  have hconst : ∀ x y, d x = d y := by
    intro x y
    exact is_const_of_deriv_eq_zero
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) x y
  have hzeroD : (∫ t in (0 : ℝ)..1, d t) = 0 := by
    change (∫ t in (0 : ℝ)..1, f t - g t) = 0
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
      (hg.intervalIntegrable 0 1), hzeroF, hzeroG]
    ring
  have hconstFun : d = fun _ => d 0 := by
    funext t
    exact hconst t 0
  have hconstIntegral := hzeroD
  rw [hconstFun, intervalIntegral.integral_const] at hconstIntegral
  simp only [sub_zero, smul_eq_mul, one_mul] at hconstIntegral
  have heq : ∀ t, f t = g t := by
    intro t
    have := hconst t 0
    have hdt : d t = d 0 := this
    rw [hconstIntegral] at hdt
    change f t - g t = 0 at hdt
    linarith
  funext t
  exact heq t

/-- Any family satisfying the stated base value, period, means, and derivative
recursion coincides with the explicit `qMNR` family. -/
theorem qMNR_unique {β : ℝ} (I : Ingredients β) (κ : ℝ)
    {m n : ℕ} (_hm : 1 ≤ m)
    (q' : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hbase : ∀ t, q' 0 t = I.jMN κ m n t - timeAvgMat (I.jMN κ m n))
    (_hperiod : ∀ r, Function.Periodic (q' r) (4 * tau β I.Λ m))
    (hmean : ∀ r, 1 ≤ r → timeAvgMat (q' r) = 0)
    (hderiv : ∀ (r : ℕ) (t : ℝ) (i j : Fin 2),
      HasDerivAt (fun s => q' (r + 1) s i j) (-(q' r t i j)) t) :
    ∀ r, q' r = I.qMNR κ m n r := by
  intro r
  induction r with
  | zero =>
      funext t
      simpa [Ingredients.qMNR] using hbase t
  | succ r ih =>
      funext t
      ext i j
      have hqcont := qMNR_entry_continuous I κ m n (r + 1) i j
      have hq'cont : Continuous (fun s => q' (r + 1) s i j) :=
        continuous_iff_continuousAt.mpr fun s => (hderiv r s i j).continuousAt
      have hderivF : ∀ s,
          HasDerivAt (fun u => q' (r + 1) u i j)
            (deriv (fun u => q' (r + 1) u i j) s) s := by
        intro s
        exact (hderiv r s i j).deriv ▸ hderiv r s i j
      have hderivG : ∀ s,
          HasDerivAt (fun u => I.qMNR κ m n (r + 1) u i j)
            (deriv (fun u => I.qMNR κ m n (r + 1) u i j) s) s := by
        intro s
        exact (qMNR_hasDerivAt I κ m n r s i j).deriv ▸
          qMNR_hasDerivAt I κ m n r s i j
      have hsame : ∀ s,
          deriv (fun u => q' (r + 1) u i j) s =
            deriv (fun u => I.qMNR κ m n (r + 1) u i j) s := by
        intro s
        rw [(hderiv r s i j).deriv,
          (qMNR_hasDerivAt I κ m n r s i j).deriv, ih]
      have hzeroQ' : (∫ s in (0 : ℝ)..1, q' (r + 1) s i j) = 0 := by
        have hz := hmean (r + 1) (by omega)
        have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hz
        simpa [timeAvgMat] using he
      have hzeroQ :
          (∫ s in (0 : ℝ)..1, I.qMNR κ m n (r + 1) s i j) = 0 := by
        have hz := qMNR_timeAvg_zero I κ m n r
        have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hz
        simpa [timeAvgMat] using he
      have heq := QMNRRecursion.eq_of_same_derivative_and_zero_average hq'cont hqcont
        hderivF hderivG hsame hzeroQ' hzeroQ
      exact congrFun heq t

end AVenhance.Infra.Section3

end
