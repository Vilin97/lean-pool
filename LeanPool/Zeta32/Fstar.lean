/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Fstar.Rho

/-! `FstarPoints → FstarInput`: the proof notes, 5.4, Lemma 12 and the
"Numerical conclusion", for layout (4,5,3) and `Fconst = −6`.

1. `massA` is nondecreasing on `[0, ∞)`, so `massA a = 1` forces `aMinus < a < aPlus`.
2. `W ≥ 0` nondecreasing (`Fstar/Wt.lean`); `ρ_a ≥ 0`, nonincreasing in `x`, nondecreasing in
`a`, and
   `W·ρ_a` interval integrable on `[0, a]` (`Fstar/Rho.lean`).
3. Lower Riemann sum on `[x₁, x₁₅]`, `x_k = aMinus·k/16`, with the pieces `[0, x₁]` and `[x₁₅,
a]` dropped (≥ 0):
   `∫₀^a Wρ_a ≥ (aMinus/16)·Σ_{j<14} Wlow_j·Rlow_{j+1}`.
4. `ellA a ≤ −159/100`, `log 3 > 549/500`; the final rational inequality by `linarith`
   (`F ≤ −6.2474 < −6`). No code copied from other repositories. -/

public section

open Real MeasureTheory
namespace Zeta32.Fstar
noncomputable section

theorem massA_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : massA a ≤ massA b := by
  have hb : 0 ≤ b := ha.trans hab
  have h1 : √(1 + a^2) ≤ √(1 + b^2) := sqrt_le_sqrt (by nlinarith)
  have hA2 : √(25 + a^2) ^ 2 = 25 + a^2 := sq_sqrt (by positivity)
  have hB2 : √(25 + b^2) ^ 2 = 25 + b^2 := sq_sqrt (by positivity)
  have hA : a ≤ √(25 + a^2) := by
    calc a = √(a^2) := (sqrt_sq ha).symm
      _ ≤ √(25 + a^2) := sqrt_le_sqrt (by nlinarith)
  have hB : b ≤ √(25 + b^2) := by
    calc b = √(b^2) := (sqrt_sq hb).symm
      _ ≤ √(25 + b^2) := sqrt_le_sqrt (by nlinarith)
  have h5 : √(25 + b^2) - √(25 + a^2) ≤ b - a := by
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hA), mul_nonneg (sub_nonneg.2 hab)
      (sub_nonneg.2 hB),
      sqrt_nonneg (25 + a^2), sqrt_nonneg (25 + b^2)]
  unfold massA
  linarith

theorem lt_aMinus_of_mass {a : ℝ} (ha : 0 < a) (hm : massA a = 1) (hlo : massA aMinus < 1) :
  aMinus < a := by
  by_contra h
  push Not at h
  have := massA_mono ha.le h
  linarith

theorem lt_aPlus_of_mass {a : ℝ} (hm : massA a = 1) (hhi : 1 < massA aPlus) : a <
  aPlus := by
  by_contra h
  push Not at h
  have := massA_mono (by norm_num [aPlus]) h
  linarith

theorem xk_pos {n : ℕ} (hn : 0 < n) : 0 < xk n := by
  unfold xk aMinus; positivity

theorem xk_le_aMinus {n : ℕ} (hn : n ≤ 16) : xk n ≤ aMinus := by
  unfold xk
  have : (n : ℝ) ≤ 16 := by exact_mod_cast hn
  have ha : (0 : ℝ) < aMinus := by norm_num [aMinus]
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

theorem xk_succ_sub (n : ℕ) : xk (n + 1) - xk n = aMinus / 16 := by
  unfold xk; push_cast; ring

theorem Rlow_nonneg (k : Fin 15) : (0 : ℝ) ≤ ((Rlow k : ℚ) : ℝ) := by
  have : (0 : ℚ) ≤ Rlow k := by fin_cases k <;> simp [Rlow] <;> norm_num
  exact_mod_cast this

theorem lowerSum_eq : (∑ j : Fin 14, Wlow j.castSucc * Rlow j.succ) = (1209903 / 500000 : ℚ) := by
  simp [Fin.sum_univ_succ, Wlow, Rlow]
  norm_num

/-- Lemma 12 lower Riemann sum. -/
theorem integral_lower {a : ℝ} (ha : aMinus < a)
    (hW : ∀ k : Fin 15, ((Wlow k : ℚ) : ℝ) ≤ Wt (xk (k.val + 1)))
    (hR : ∀ k : Fin 15, ((Rlow k : ℚ) : ℝ) ≤ rhoA aMinus (xk (k.val + 1))) :
    (aMinus / 16) * (((∑ j : Fin 14, Wlow j.castSucc * Rlow j.succ : ℚ)) : ℝ)
      ≤ ∫ x in (0:ℝ)..a, Wt x * rhoA a x := by
  have ham : (0 : ℝ) < aMinus := by norm_num [aMinus]
  have ha0 : 0 < a := ham.trans ha
  set f := fun x => Wt x * rhoA a x with hf
  have hint := intervalIntegrable_Wt_rhoA ha0
  have hsub : ∀ c d : ℝ, 0 ≤ c → c ≤ a → 0 ≤ d → d ≤ a → IntervalIntegrable f volume c d :=
    fun c d hc hca hd hda => hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hc, hca⟩)) (Set.mem_uIcc.mpr (Or.inl ⟨hd, hda⟩)))
  have hx0 : ∀ n : ℕ, 0 ≤ xk n := fun n => by unfold xk aMinus; positivity
  have hxa : ∀ n : ℕ, n ≤ 16 → xk n ≤ a := fun n hn => (xk_le_aMinus hn).trans ha.le
  have hsplit : ∫ x in (0:ℝ)..a, f x
      = (∫ x in (0:ℝ)..xk 1, f x) + (∫ x in xk 1..xk 15, f x) + ∫ x in xk 15..a, f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (hsub _ _ le_rfl ha0.le (hx0 1) (hxa 1 (by norm_num))) (hsub _ _ (hx0 1) (hxa 1 (by
          norm_num))
          (hx0 15) (hxa 15 (by norm_num))),
      intervalIntegral.integral_add_adjacent_intervals
        (hsub _ _ le_rfl ha0.le (hx0 15) (hxa 15 (by norm_num))) (hsub _ _ (hx0 15) (hxa 15 (by
          norm_num))
          ha0.le le_rfl)]
  have hfirst : 0 ≤ ∫ x in (0:ℝ)..xk 1, f x :=
    intervalIntegral.integral_nonneg (hx0 1) (fun x hx => Wt_mul_rhoA_nonneg hx.1 (hx.2.trans
      (hxa 1 (by norm_num))))
  have hlast : 0 ≤ ∫ x in xk 15..a, f x :=
    intervalIntegral.integral_nonneg (hxa 15 (by norm_num)) (fun x hx => Wt_mul_rhoA_nonneg
      ((hx0 15).trans hx.1) hx.2)
  have hmid : ∫ x in xk 1..xk 15, f x = ∑ j : Fin 14, ∫ x in xk (j.val + 1)..xk (j.val + 1 + 1),
    f x := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ∫ x in xk (k + 1)..xk (k + 1 + 1), f x) 14]
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k => xk (k + 1))]
    intro k hk
    exact hsub _ _ (hx0 _) (hxa _ (by omega)) (hx0 _) (hxa _ (by omega))
  have hpiece : ∀ j : Fin 14, (aMinus / 16) * (((Wlow j.castSucc : ℚ) : ℝ) * ((Rlow j.succ : ℚ)
    : ℝ))
      ≤ ∫ x in xk (j.val + 1)..xk (j.val + 1 + 1), f x := by
    intro j
    have hj := j.isLt
    have hle : xk (j.val + 1) ≤ xk (j.val + 1 + 1) := by linarith [xk_succ_sub (j.val + 1)]
    calc (aMinus / 16) * (((Wlow j.castSucc : ℚ) : ℝ) * ((Rlow j.succ : ℚ) : ℝ))
        = ∫ _ in xk (j.val + 1)..xk (j.val + 1 + 1), (((Wlow j.castSucc : ℚ) : ℝ) * ((Rlow
          j.succ : ℚ) : ℝ)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, xk_succ_sub]
      _ ≤ ∫ x in xk (j.val + 1)..xk (j.val + 1 + 1), f x := by
          apply intervalIntegral.integral_mono_on hle intervalIntegrable_const
            (hsub _ _ (hx0 _) (hxa _ (by omega)) (hx0 _) (hxa _ (by omega)))
          intro x hx
          have hxp : 0 < x := (xk_pos (by omega)).trans_le hx.1
          have hw : ((Wlow j.castSucc : ℚ) : ℝ) ≤ Wt x := by
            have := hW j.castSucc
            rw [Fin.val_castSucc] at this
            exact this.trans (Wt_mono (hx0 _) hx.1)
          have hr : ((Rlow j.succ : ℚ) : ℝ) ≤ rhoA a x := by
            have h1 := hR j.succ
            rw [Fin.val_succ] at h1
            have hxk : xk (j.val + 1 + 1) ≤ aMinus := xk_le_aMinus (by omega)
            exact h1.trans ((rhoA_mono_a (xk_pos (by omega)) hxk ha.le).trans
              (rhoA_anti_x hxp hx.2 (hxk.trans ha.le)))
          exact mul_le_mul hw hr (Rlow_nonneg _) (Wt_nonneg hxp.le)
  rw [hsplit, hmid]
  push_cast
  rw [Finset.mul_sum]
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpiece j)
  linarith

theorem fstarInput_of_points : FstarPoints → FstarInput := by
  rintro ⟨hm1, hm2, hell, hlog3, hpts⟩ a ha hma
  have hlo := lt_aMinus_of_mass ha hma hm1
  have hhi := lt_aPlus_of_mass hma hm2
  have hellA := hell a ⟨hlo.le, hhi.le⟩
  have hI := integral_lower hlo (fun k => (hpts k).1) (fun k => (hpts k).2)
  rw [lowerSum_eq] at hI
  norm_num [aMinus] at hI
  linarith

end
end Zeta32.Fstar
