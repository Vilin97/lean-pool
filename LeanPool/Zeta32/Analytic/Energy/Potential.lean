/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Discrete
public import LeanPool.Zeta32.Analytic.Energy.Poisson
public import LeanPool.Zeta32.Analytic.Energy.CIntegrals

/-! The comparison density `rhoA a` (the proof notes (8′), (11′), (15′)).

`rhoA a = ∫ g(c) ρ_c dc` (CIntegrals); Tonelli/Fubini in `(t, c)` turns `∫ φ · rhoA` into `∫
g(c) ∫ φ · ρ_c`.
With the per-component potentials (Poisson) and the `g`-integrals of `kC`, `wC` this gives
`2L − W = ℓ` on `[-a, a]`, `2L − W ≤ ℓ` everywhere, and `2I − W = ℓ`, `ℓ = ellA a`, when
`massA a = 1`. -/

public section

open Real MeasureTheory Set Filter
open scoped Interval

namespace Zeta32.Analytic.EnergyI
noncomputable section

variable {a : ℝ}

theorem rhoC_nonneg (ha : 0 < a) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 0 ≤ rhoC a c t := by
  unfold rhoC
  have := uC_pos ha c
  exact div_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (by positivity)

theorem measurable_rhoC (a : ℝ) : Measurable (fun p : ℝ × ℝ => rhoC a p.2 p.1) := by
  unfold rhoC uC
  fun_prop

/-- Mass of the component: `∫ ρ_c = (1 − c/u_c)/2`. -/
theorem mass_rhoC (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    ∫ t in (-a)..a, rhoC a c t = (1 - c / uC a c) / 2 := by
  have h := integral_rhoC_eq ha hc (fun _ => 1)
    (by simpa using (continuous_fC ha hc).intervalIntegrable 0 π)
  simp only [one_mul] at h
  rw [h]
  have hp1 := continuous_PK (PK_betaC_norm ha hc _ (Or.inl rfl))
  have hp2 := continuous_PK (PK_betaC_norm ha hc _ (Or.inr rfl))
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hpt : ∀ θ, fC a c θ = (1 / (8 * π)) * PK (Complex.I * (betaC a c : ℝ)) θ +
      (1 / (8 * π)) * PK (Complex.I * ((-betaC a c : ℝ))) θ - c / uC a c / (4 * π) := by
    intro θ
    have h := fC_eq_PK ha hc θ
    have : fC a c θ = ((PK (Complex.I * (betaC a c : ℝ)) θ + PK (Complex.I * ((-betaC a c : ℝ)))
      θ) / 2
      - c / uC a c) / (4 * π) := by rw [← h]; field_simp
    rw [this]; field_simp; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub (((hp1.intervalIntegrable _ _).const_mul _).add
      ((hp2.intervalIntegrable _ _).const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_add ((hp1.intervalIntegrable _ _).const_mul _)
      ((hp2.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_PK (PK_betaC_norm ha hc _ (Or.inl rfl)), integral_PK (PK_betaC_norm ha hc _ (Or.inr
      rfl)),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp
  ring

theorem ae_good :
    ∀ᵐ t ∂(volume.restrict (Ioo (-a) a)), t ≠ 0 ∧ |t| < a := by
  filter_upwards [ae_restrict_of_ae ae_ne_zero, ae_restrict_mem measurableSet_Ioo] with t ht htI
  exact ⟨ht, abs_lt.mpr htI⟩

theorem intervalIntegral_eq_Ioo (f : ℝ → ℝ) (ha : 0 < a) :
    ∫ t in (-a)..a, f t = ∫ t in Ioo (-a) a, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]

/-- Fubini in `(t, c)`: `∫ φ · rhoA = ∫ g(c) ∫ φ · ρ_c`. -/
theorem fubini_rhoA (ha : 0 < a) (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ : IntervalIntegrable (fun t => |φ t| * rhoA a t) volume (-a) a) :
    IntegrableOn (fun c => gtil c * ∫ t in (-a)..a, φ t * rhoC a c t) (Ioi 0) ∧
      ∫ t in (-a)..a, φ t * rhoA a t = ∫ c in Ioi (0:ℝ), gtil c * ∫ t in (-a)..a, φ t * rhoC a c
        t := by
  set μ := volume.restrict (Ioo (-a) a)
  set ν := volume.restrict (Ioi (0:ℝ))
  let F : ℝ → ℝ → ℝ := fun t c => φ t * (gtil c * rhoC a c t)
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable fun p : ℝ × ℝ => φ p.1 := hφm.comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ => gtil p.2 := measurable_gtil.comp measurable_snd
    exact h1.mul (h2.mul (measurable_rhoC a))
  have hgood := ae_good (a := a)
  have hinner : ∀ t, t ≠ 0 → |t| < a → Integrable (fun c => F t c) ν ∧
      ∫ c, F t c ∂ν = φ t * rhoA a t := by
    intro t ht hta
    obtain ⟨h1, h2⟩ := integral_gtil_rhoC ha ht hta
    exact ⟨h1.const_mul (φ t), by simp only [F]; rw [integral_const_mul, h2]⟩
  have hnorm : ∀ t, t ≠ 0 → |t| < a → ∫ c, ‖F t c‖ ∂ν = |φ t| * rhoA a t := by
    intro t ht hta
    obtain ⟨h1, h2⟩ := integral_gtil_rhoC ha ht hta
    have e : (fun c => ‖F t c‖) =ᵐ[ν] fun c => |φ t| * (gtil c * rhoC a c t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
      simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (gtil_pos c),
        abs_of_nonneg (rhoC_nonneg ha (le_of_lt hc) t)]
    rw [integral_congr_ae e, integral_const_mul, h2]
  have hφ' : Integrable (fun t => |φ t| * rhoA a t) μ := by
    have := hφ.def'
    rw [uIoc_of_le (by linarith)] at this
    exact this.mono_set Ioo_subset_Ioc_self
  have hint : Integrable (Function.uncurry F) (μ.prod ν) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hgood] with t ht
      exact (hinner t ht.1 ht.2).1
    · refine hφ'.congr ?_
      filter_upwards [hgood] with t ht
      exact (hnorm t ht.1 ht.2).symm
  have hswap := integral_integral_swap hint
  have hleft : ∫ t in (-a)..a, φ t * rhoA a t = ∫ t, ∫ c, F t c ∂ν ∂μ := by
    rw [intervalIntegral_eq_Ioo _ ha]
    refine integral_congr_ae ?_
    filter_upwards [hgood] with t ht
    exact (hinner t ht.1 ht.2).2.symm
  have hright : ∀ c, ∫ t, F t c ∂μ = gtil c * ∫ t in (-a)..a, φ t * rhoC a c t := by
    intro c
    rw [intervalIntegral_eq_Ioo _ ha, ← integral_const_mul]
    congr 1; funext t; simp only [F]; ring
  have hIc : Integrable (fun c => ∫ t, F t c ∂μ) ν := hint.integral_prod_right
  refine ⟨?_, ?_⟩
  · exact hIc.congr (Filter.Eventually.of_forall hright)
  · rw [hleft, hswap]
    exact integral_congr_ae (Filter.Eventually.of_forall hright)

theorem mass_rhoA (ha : 0 < a) : ∫ t in (-a)..a, rhoA a t = massA a := by
  have h := fubini_rhoA ha (fun _ => 1) measurable_const
    (by simpa using intervalIntegrable_rhoA ha)
  simp only [one_mul] at h
  rw [h.2, setIntegral_congr_fun measurableSet_Ioi (fun c hc => by rw [mass_rhoC ha hc])]
  exact (integral_gtil_mass ha).2

theorem potA_eq_integral (ha : 0 < a) (x : ℝ) :
    IntegrableOn (fun c => gtil c * potC a c x) (Ioi 0) ∧
      potA a x = ∫ c in Ioi (0:ℝ), gtil c * potC a c x := by
  have h := fubini_rhoA ha (fun t => Real.log |x - t|) (by fun_prop)
    (intervalIntegrable_abs_log_mul_rhoA ha x)
  exact ⟨h.1, h.2⟩

/-- The mass equation has a positive root. -/
theorem exists_massA_eq_one : ∃ a : ℝ, 0 < a ∧ massA a = 1 := by
  have hcont : Continuous massA := by unfold massA; fun_prop
  have h0 : massA 0 = 0 := by
    unfold massA
    rw [show (1:ℝ) + 0^2 = 1^2 by norm_num, show (25:ℝ) + 0^2 = 5^2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
    norm_num
  have h3 : 1 < massA 3 := by
    unfold massA
    have e1 : (1:ℝ) + 3^2 = 10 := by norm_num
    have e2 : (25:ℝ) + 3^2 = 34 := by norm_num
    rw [e1, e2]
    have s1 : (31/10 : ℝ) < √10 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have s2 : √34 < 59/10 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    nlinarith
  obtain ⟨a, ha, hma⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 3) hcont.continuousOn
    ⟨by rw [h0]; norm_num, h3.le⟩
  refine ⟨a, ?_, hma⟩
  rcases ha.1.lt_or_eq with h | h
  · exact h
  · subst h; rw [h0] at hma; norm_num at hma

theorem rhoA_good (ha : 0 < a) (hm : massA a = 1) : GoodDensity (rhoA a) a where
  pos := ha
  meas := measurable_rhoA a
  nonneg := by
    filter_upwards [ae_ne_zero] with t ht htI
    exact rhoA_nonneg_of_ne ht (abs_le.mpr ⟨htI.1, htI.2⟩)
  int := intervalIntegrable_rhoA ha
  int2 := intervalIntegrable_rhoA_sq ha
  mass := by rw [mass_rhoA ha, hm]

/-- (8′) on the support: `2L − W = ℓ`. -/
theorem potA_eq (ha : 0 < a) (hm : massA a = 1) {x : ℝ} (hx : |x| ≤ a) :
    2 * potA a x = ellA a + Wt |x| := by
  obtain ⟨hi, he⟩ := potA_eq_integral ha x
  obtain ⟨k1, k2⟩ := integral_gtil_kC ha
  obtain ⟨w1, w2⟩ := integral_gtil_wC x
  have hpt : ∀ c ∈ Ioi (0:ℝ), gtil c * potC a c x =
      (1/2) * (gtil c * kC a c) + (1/2) * (gtil c * wC c x) := by
    intro c hc
    have := two_potC_inside ha hc hx
    linear_combination (gtil c / 2) * this
  rw [he, setIntegral_congr_fun measurableSet_Ioi hpt, integral_add (k1.const_mul _)
    (w1.const_mul _),
    integral_const_mul, integral_const_mul, k2, w2, hm]
  ring

/-- (8′) everywhere: `2L − W ≤ ℓ`. -/
theorem potA_le (ha : 0 < a) (hm : massA a = 1) (x : ℝ) :
    2 * potA a x ≤ ellA a + Wt |x| := by
  obtain ⟨hi, he⟩ := potA_eq_integral ha x
  obtain ⟨k1, k2⟩ := integral_gtil_kC ha
  obtain ⟨w1, w2⟩ := integral_gtil_wC x
  have hle : ∫ c in Ioi (0:ℝ), gtil c * potC a c x ≤
      ∫ c in Ioi (0:ℝ), ((1/2) * (gtil c * kC a c) + (1/2) * (gtil c * wC c x)) := by
    refine setIntegral_mono_on hi ((k1.const_mul _).add (w1.const_mul _)) measurableSet_Ioi ?_
    intro c hc
    have := two_potC_le ha hc x
    have hg := gtil_pos c
    nlinarith
  rw [integral_add (k1.const_mul _) (w1.const_mul _), integral_const_mul, integral_const_mul,
    k2, w2,
    hm] at hle
  rw [he]
  linarith

/-- Crude growth of the potential. -/
theorem potA_le_log (ha : 0 < a) (hm : massA a = 1) (x : ℝ) :
    potA a x ≤ Real.log (|x| + a) := by
  have hmass : ∫ t in (-a)..a, rhoA a t = 1 := by rw [mass_rhoA ha, hm]
  have hle : potA a x ≤ ∫ t in (-a)..a, Real.log (|x| + a) * rhoA a t := by
    unfold potA potD
    refine intervalIntegral.integral_mono_ae_restrict (by linarith)
      (intervalIntegrable_log_mul_rhoA ha x)
      ((intervalIntegrable_rhoA ha).const_mul _) ?_
    filter_upwards [ae_restrict_of_ae ae_ne_zero, ae_restrict_of_ae ((volume : Measure ℝ).ae_ne x),
      ae_restrict_mem measurableSet_Icc] with t ht0 htx htI
    have hta : |t| ≤ a := abs_le.mpr ⟨htI.1, htI.2⟩
    have hρ := rhoA_nonneg_of_ne ht0 hta
    have hpos : 0 < |x - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm htx))
    have hle : |x - t| ≤ |x| + a := (abs_sub _ _).trans (by linarith)
    exact mul_le_mul_of_nonneg_right (Real.log_le_log hpos hle) hρ
  rw [intervalIntegral.integral_const_mul, hmass, mul_one] at hle
  exact hle

theorem intervalIntegrable_Wt_abs_rhoA (ha : 0 < a) :
    IntervalIntegrable (fun x => Wt |x| * rhoA a x) volume 0 a := by
  refine (Fstar.intervalIntegrable_Wt_rhoA ha).congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [uIoc_of_le ha.le] at hx
  rw [abs_of_pos hx.1]

/-- (15′): `2I − W = ℓ`, with `W = 2∫₀^a Wt·rhoA`. -/
theorem IA_eq (ha : 0 < a) (hm : massA a = 1) :
    2 * IA a = ellA a + 2 * ∫ x in (0:ℝ)..a, Wt x * rhoA a x := by
  have hmass : ∫ t in (-a)..a, rhoA a t = 1 := by rw [mass_rhoA ha, hm]
  have hI : IA a = ∫ x in (-a)..a, ((ellA a + Wt |x|) / 2) * rhoA a x := by
    unfold IA ID
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have := potA_eq ha hm (abs_le.mpr ⟨hx.1, hx.2⟩)
    change potA a x * rhoA a x = _
    rw [show potA a x = (ellA a + Wt |x|) / 2 by linarith]
  have hW0 := intervalIntegrable_Wt_abs_rhoA ha
  have hWneg : IntervalIntegrable (fun x => Wt |x| * rhoA a x) volume (-a) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hW0
    simp only [neg_zero, abs_neg, rhoA_neg] at h
    exact h.symm
  have hsym : ∫ x in (-a)..0, Wt |x| * rhoA a x = ∫ x in (0:ℝ)..a, Wt |x| * rhoA a x := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun x => Wt |x| * rhoA a x)
    simp only [neg_zero, abs_neg, rhoA_neg] at this
    exact this.symm
  have hWall : ∫ x in (-a)..a, Wt |x| * rhoA a x = 2 * ∫ x in (0:ℝ)..a, Wt x * rhoA a x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hWneg hW0, hsym]
    have : ∫ x in (0:ℝ)..a, Wt |x| * rhoA a x = ∫ x in (0:ℝ)..a, Wt x * rhoA a x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ha.le] at hx
      simp only [abs_of_nonneg hx.1]
    rw [this]; ring
  have hsplit : ∫ x in (-a)..a, ((ellA a + Wt |x|) / 2) * rhoA a x =
      (ellA a / 2) * (∫ x in (-a)..a, rhoA a x) + (1/2) * ∫ x in (-a)..a, Wt |x| * rhoA a x := by
    have e : ∫ x in (-a)..a, ((ellA a + Wt |x|) / 2) * rhoA a x =
        ∫ x in (-a)..a, ((ellA a / 2) * rhoA a x + (1/2) * (Wt |x| * rhoA a x)) :=
      intervalIntegral.integral_congr (fun x _ => by ring)
    rw [e, intervalIntegral.integral_add ((intervalIntegrable_rhoA ha).const_mul _)
      ((hWneg.trans hW0).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hI, hsplit]
  linear_combination (ellA a) * hmass + hWall

end
end Zeta32.Analytic.EnergyI

end
