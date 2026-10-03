/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.Approx
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.JMNPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp

/-! # Facts about `JHat_m` and the replacement `J_m → JHat_m` of `e.TJT.break`

Source: `enhance.tex` 3040–3190 (`e.Jhat`, `e.JJhat`, `e.jkmn`, `e.Lmn.def`) and 8640–8780
(`e.TJT.break`).  `JHat_m^κ = κ I + ∑_{n<N_*} L_{m,n} 𝐣_{m,n}` is continuous and `4τ''_m`-periodic,
is within `a_m² ε_m⁴/κ` of `κ I`, and replacing `J_m` by `JHat_m` in the time-averaged quadratic
    form
costs the `e.JJhat` error. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance AVenhance.Infra.Section3

/-- Public continuity of `JHat` entries. -/
theorem Jhat_entry_continuous_pub {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ}
    (hκ : 0 < κ) (i j : Fin 2) : Continuous (fun t => I.Jhat κ m t i j) := by
  unfold Ingredients.Jhat
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply continuous_const.add
  apply continuous_finsetSum
  intro n _
  exact (LMN_contDiff I hm hκ n).continuous.mul
    ((continuous_apply j).comp ((continuous_apply i).comp (jMN_continuous I m n κ)))

theorem Jhat_entry_periodic {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ)
    (i j : Fin 2) : Function.Periodic (fun t => I.Jhat κ m t i j) (4 * tauPP β I.Λ m) := by
  obtain ⟨k, hk⟩ := four_tauPP_eq_nat_mul_four_tau I.one_lt_beta I.beta_lt
    I.two_pow_seven_le hm
  intro t
  have hL (n : ℕ) : I.LMN κ m n (t + 4 * tauPP β I.Λ m) = I.LMN κ m n t := by
    have h := (LMN_periodic I κ m n).nat_mul 4 t
    simpa only [Nat.cast_ofNat] using h
  have hj (n : ℕ) : I.jMN κ m n (t + 4 * tauPP β I.Λ m) = I.jMN κ m n t := by
    have h := (jMN_period_four_tau I (m := m) κ n).nat_mul k t
    rw [hk]
    exact h
  unfold Ingredients.Jhat
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hL, hj]

/-- Abstract-real core of the `L_{m,n} 𝐣_{m,n}` size: `n! 2ⁿ (E/(2π²κ))` times
`(2π²AE/n!)(E/(4π²κ))ⁿ (C/τⁿ)` is at most `C A E²/κ` once `E/(κτ) ≤ 1`. -/
theorem LMN_mul_jMN_abs_bound (n : ℕ) {A E κ τ C : ℝ} (hA : 0 ≤ A) (hE : 0 < E) (hκ : 0 < κ)
    (hτ : 0 < τ) (hC : 0 ≤ C) (hr : E / (κ * τ) ≤ 1) :
    ((n.factorial : ℝ) * 2 ^ n * (4 * Real.pi ^ 2 * κ / E / 2)⁻¹) *
      ((2 * Real.pi ^ 2 * A * E / (n.factorial : ℝ) * (E / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (C / τ ^ n)) ≤ C * (A * E ^ 2 / κ) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hq : 0 ≤ 2 / (4 * Real.pi ^ 2) * (E / (κ * τ)) := by positivity
  have hq1 : 2 / (4 * Real.pi ^ 2) * (E / (κ * τ)) ≤ 1 := by
    have h2 : 2 / (4 * Real.pi ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    calc _ ≤ 1 * 1 := mul_le_mul h2 hr (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have heq : ((n.factorial : ℝ) * 2 ^ n * (4 * Real.pi ^ 2 * κ / E / 2)⁻¹) *
      ((2 * Real.pi ^ 2 * A * E / (n.factorial : ℝ) * (E / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (C / τ ^ n)) =
      C * (A * E ^ 2 / κ) * (2 / (4 * Real.pi ^ 2) * (E / (κ * τ))) ^ n := by
    rw [mul_pow, div_pow, div_pow, div_pow]
    field_simp
    rw [mul_pow (4 * Real.pi ^ 2) κ n, mul_pow κ τ n]
    ring
  rw [heq]
  calc _ ≤ C * (A * E ^ 2 / κ) * 1 := by
        gcongr
        exact pow_le_one₀ hq hq1
    _ = _ := mul_one _

/-- `sup |JHat_m^κ - κ I| ≲ a_m² ε_m⁴ / κ` when `ε_m²/(κ τ_m) ≤ 1`. -/
theorem Jhat_sub_kappa_entry_abs_le (β C₀ : ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
    ∀ m : ℕ, 1 ≤ m → ∀ κ : ℝ, 0 < κ →
      epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1 →
      ∀ t : ℝ, ∀ i j : Fin 2,
        |(I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤
          K * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
  refine ⟨Nstar β * |C₀|, by positivity, ?_⟩
  intro I hC _ _ m hm κ hκ hr t i j
  have hC0 : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hτ := I.tau_pos' m
  have hε : 0 < epsilon β I.Λ m ^ 2 :=
    pow_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le)) 2
  have ha : 0 ≤ a β I.Λ m ^ 2 := sq_nonneg _
  have hterm (n : ℕ) (hn : n ∈ Finset.range (Nstar β)) :
      |I.LMN κ m n t * I.jMN κ m n t i j| ≤
        I.Czeta * (a β I.Λ m ^ 2 * (epsilon β I.Λ m ^ 2) ^ 2 / κ) := by
    have hn' : n ≤ Nstar β := (Finset.mem_range.mp hn).le
    rw [abs_mul]
    refine le_trans (mul_le_mul (LMN_abs_le I hm hκ n t) (jMN_entry_abs_le I m hn' hκ t i j)
      (abs_nonneg _) (by positivity)) ?_
    exact LMN_mul_jMN_abs_bound n ha hε hκ hτ hC0 hr
  have hsum : (I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j =
      ∑ n ∈ Finset.range (Nstar β), I.LMN κ m n t * I.jMN κ m n t i j := by
    unfold Ingredients.Jhat
    simp only [add_sub_cancel_left, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4 : epsilon β I.Λ m ^ 4 = (epsilon β I.Λ m ^ 2) ^ 2 := by ring
  rw [h4]
  have hcb : I.Czeta ≤ |C₀| := hC.trans (le_abs_self C₀)
  have hnn : 0 ≤ a β I.Λ m ^ 2 * (epsilon β I.Λ m ^ 2) ^ 2 / κ := by positivity
  calc (Nstar β : ℝ) * (I.Czeta * (a β I.Λ m ^ 2 * (epsilon β I.Λ m ^ 2) ^ 2 / κ))
      ≤ (Nstar β : ℝ) * (|C₀| * (a β I.Λ m ^ 2 * (epsilon β I.Λ m ^ 2) ^ 2 / κ)) := by
        gcongr
    _ = _ := by ring

/-- Entrywise difference of time averages is the average of the entrywise difference. -/
theorem timeAvgMat_sub_entry_eq_integral' {F G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (i j : Fin 2)
    (hf : Continuous (fun t => F t i j)) (hg : Continuous (fun t => G t i j)) :
    (timeAvgMat F - timeAvgMat G) i j = ∫ t in (0 : ℝ)..1, (F t - G t) i j := by
  simp only [timeAvgMat, Matrix.sub_apply, Matrix.of_apply]
  exact (intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
    (hg.intervalIntegrable 0 1)).symm

theorem Jhat_sub_timeAvg_entry_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    {κ : ℝ} (hκ : 0 < κ) {B : ℝ}
    (hB : ∀ t i j, |(I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤ B)
    (t : ℝ) (i j : Fin 2) :
    |(I.Jhat κ m t - timeAvgMat (I.Jhat κ m)) i j| ≤ 2 * B := by
  have hc := Jhat_entry_continuous_pub I hm hκ i j
  have havg : (timeAvgMat (I.Jhat κ m) - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j =
      ∫ s in (0 : ℝ)..1, (I.Jhat κ m s - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j := by
    have h := timeAvgMat_sub_entry_eq_integral' (F := I.Jhat κ m)
      (G := fun _ => κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j hc continuous_const
    have hconst : timeAvgMat (fun _ : ℝ => κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext a b
      simp [timeAvgMat]
    rwa [hconst] at h
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun s => (I.Jhat κ m s - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j)
    (C := B) (fun s _ => by simpa only [Real.norm_eq_abs] using hB s i j)
  rw [← havg] at hint
  simp only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
  have hsplit : (I.Jhat κ m t - timeAvgMat (I.Jhat κ m)) i j =
      (I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j -
        (timeAvgMat (I.Jhat κ m) - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j := by
    simp only [Matrix.sub_apply]
    ring
  rw [hsplit]
  calc _ ≤ |(I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| +
        |(timeAvgMat (I.Jhat κ m) - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| := abs_sub _ _
    _ ≤ B + B := add_le_add (hB t i j) hint
    _ = 2 * B := by ring

/-- `e.TJT.break`: replacing `J_m` by `JHat_m` costs the `e.JJhat` error. -/
theorem TJT_break {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    |(∫ t in (0 : ℝ)..1, gradQuad T (I.flux κm m t) t) -
        ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat fun s => I.flux κm m s) t| ≤
      |(∫ t in (0 : ℝ)..1, gradQuad T (I.Jhat κm m t) t) -
          ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat (I.Jhat κm m)) t| +
        4 * ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
          (epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m)) ^ Nstar β) *
          ∫ t in (0 : ℝ)..1, ∫ x in unitCube, vecNormSq (spaceGrad (T t) x) := by
  set c0 : ℝ := (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
    (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
    (epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m)) ^ Nstar β with hc0
  have hg : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    (spaceGrad_continuousOn hT).mono (Set.prod_mono Set.Icc_subset_Ici_self subset_rfl)
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (spaceGrad (T t)) := fun t ht =>
    hg.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht, mem_univ _⟩
  have hQ : ContinuousOn (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (T t) x))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_unitCube
      (h := fun t x => vecNormSq (spaceGrad (T t) x))
      (continuous_vecNormSq_two.comp_continuousOn hg)
  have hfl : ∀ i j, Continuous fun t => I.flux κm m t i j :=
    fun i j => flux_entry_time_continuous I hm κm i j
  have hJc : ∀ i j, Continuous fun t => I.Jhat κm m t i j :=
    fun i j => Jhat_entry_continuous_pub I hm hκm i j
  have hg1 := continuousOn_gradQuad hg (M := fun t => I.flux κm m t)
    fun i j => (hfl i j).continuousOn
  have hh1 := continuousOn_gradQuad hg (M := fun t => I.Jhat κm m t)
    fun i j => (hJc i j).continuousOn
  have hg2 := continuousOn_gradQuad hg (M := fun _ => timeAvgMat fun s => I.flux κm m s)
    fun _ _ => continuousOn_const
  have hh2 := continuousOn_gradQuad hg (M := fun _ => timeAvgMat (I.Jhat κm m))
    fun _ _ => continuousOn_const
  -- the entrywise bound of the difference
  have hent (t : ℝ) (i j : Fin 2) : |(I.flux κm m t - I.Jhat κm m t) i j| ≤ c0 :=
    flux_sub_Jhat_entry_abs_le I hm hκm t i j
  have havg (i j : Fin 2) :
      |(timeAvgMat (fun s => I.flux κm m s) - timeAvgMat (I.Jhat κm m)) i j| ≤ c0 := by
    rw [timeAvgMat_sub_entry_eq_integral' i j (hfl i j) (hJc i j)]
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := fun s => (I.flux κm m s - I.Jhat κm m s) i j)
      (C := c0) (fun s _ => by simpa only [Real.norm_eq_abs] using hent s i j)
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hint
  set D : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t =>
    (I.flux κm m t - I.Jhat κm m t) -
      (timeAvgMat (fun s => I.flux κm m s) - timeAvgMat (I.Jhat κm m)) with hD
  have hDent (t : ℝ) (i j : Fin 2) : |D t i j| ≤ 2 * c0 := by
    simp only [hD, Matrix.sub_apply]
    calc _ ≤ |(I.flux κm m t - I.Jhat κm m t) i j| +
          |(timeAvgMat (fun s => I.flux κm m s) - timeAvgMat (I.Jhat κm m)) i j| := by
          simpa only [Matrix.sub_apply] using abs_sub
            ((I.flux κm m t - I.Jhat κm m t) i j)
            ((timeAvgMat (fun s => I.flux κm m s) - timeAvgMat (I.Jhat κm m)) i j)
      _ ≤ c0 + c0 := add_le_add (hent t i j) (havg i j)
      _ = 2 * c0 := by ring
  have hDpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, gradQuad T (D t) t =
      (gradQuad T (I.flux κm m t) t - gradQuad T (I.Jhat κm m t) t) -
        (gradQuad T (timeAvgMat fun s => I.flux κm m s) t -
          gradQuad T (timeAvgMat (I.Jhat κm m)) t) := by
    intro t ht
    simp only [hD]
    rw [gradQuad_sub T (hslice t ht), gradQuad_sub T (hslice t ht),
      gradQuad_sub T (hslice t ht)]
  have hDint : (∫ t in (0 : ℝ)..1, gradQuad T (D t) t) =
      ((∫ t in (0 : ℝ)..1, gradQuad T (I.flux κm m t) t) -
        ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat fun s => I.flux κm m s) t) -
      ((∫ t in (0 : ℝ)..1, gradQuad T (I.Jhat κm m t) t) -
        ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat (I.Jhat κm m)) t) := by
    have i1 := intervalIntegrable_of_continuousOn_Icc hg1
    have i2 := intervalIntegrable_of_continuousOn_Icc hg2
    have i3 := intervalIntegrable_of_continuousOn_Icc hh1
    have i4 := intervalIntegrable_of_continuousOn_Icc hh2
    rw [intervalIntegral.integral_congr fun t ht => hDpt t (by
      rwa [Set.uIcc_of_le zero_le_one] at ht),
      intervalIntegral.integral_sub (i1.sub i3) (i2.sub i4),
      intervalIntegral.integral_sub i1 i3, intervalIntegral.integral_sub i2 i4]
    ring
  have hbound : |∫ t in (0 : ℝ)..1, gradQuad T (D t) t| ≤
      4 * c0 * ∫ t in (0 : ℝ)..1, ∫ x in unitCube, vecNormSq (spaceGrad (T t) x) := by
    have hQint := intervalIntegrable_of_continuousOn_Icc hQ
    have h := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (f := fun t => gradQuad T (D t) t)
      (g := fun t => 4 * c0 * ∫ x in unitCube, vecNormSq (spaceGrad (T t) x))
      (Filter.Eventually.of_forall fun t ht => by
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        rw [Real.norm_eq_abs]
        have := abs_gradQuad_le (hslice t ht') (hDent t)
        linarith)
      (hQint.const_mul (4 * c0))
    rw [intervalIntegral.integral_const_mul] at h
    simpa only [Real.norm_eq_abs] using h
  have hsplit : ((∫ t in (0 : ℝ)..1, gradQuad T (I.flux κm m t) t) -
        ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat fun s => I.flux κm m s) t) =
      ((∫ t in (0 : ℝ)..1, gradQuad T (I.Jhat κm m t) t) -
        ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat (I.Jhat κm m)) t) +
      ∫ t in (0 : ℝ)..1, gradQuad T (D t) t := by
    rw [hDint]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add_right hbound _)

end AVenhance.Infra.Section5.LeftToShow

end
