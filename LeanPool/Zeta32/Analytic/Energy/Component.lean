/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Defs
public import LeanPool.Zeta32.Analytic.Energy.PoissonKernel

/-! The component `ρ_c` of the proof notes (8′) in angular coordinates.

With `t = a cos θ`, `ρ_c(t) dt` on `(-a, a)` becomes `fC θ dθ` on `(0, 2π)` (each `t` twice), and
`4π fC = (P(iβ) + P(−iβ))/2 − c/u_c` with `β = a/(u_c + c)` and `P` the Poisson kernel of the
unit disc:
the balayage of `δ_{±ic}` onto `[-a, a]` minus a multiple of the arcsine measure
(GLOBAL-INTEGRAL-v1 §5). -/

public section

open Real MeasureTheory Set

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-- `β = a/(u_c + c)`: `±iβ` are the preimages of `±ic` inside the unit disc under `w ↦ (a/2)(w
+ 1/w)`. -/
@[expose]
def betaC (a c : ℝ) : ℝ := a / (uC a c + c)

/-- Angular density of `ρ_c`. -/
def fC (a c θ : ℝ) : ℝ :=
  c * a^2 * Real.sin θ ^ 2 / (4 * π * uC a c * (a^2 * Real.cos θ ^ 2 + c^2))

section basic
variable {a c : ℝ}

theorem uC_sq (a c : ℝ) : uC a c ^ 2 = c^2 + a^2 := by
  unfold uC; rw [Real.sq_sqrt (by positivity)]

theorem uC_pos (ha : 0 < a) (c : ℝ) : 0 < uC a c := by
  unfold uC; exact Real.sqrt_pos.mpr (by positivity)

theorem c_lt_uC (ha : 0 < a) (hc : 0 ≤ c) : c < uC a c := by
  have h := uC_sq a c
  have hp := uC_pos ha c
  nlinarith

theorem a_lt_uC (ha : 0 < a) (hc : 0 < c) : a < uC a c := by
  have h := uC_sq a c
  have hp := uC_pos ha c
  nlinarith

theorem betaC_pos (ha : 0 < a) (hc : 0 ≤ c) : 0 < betaC a c := by
  unfold betaC; have := uC_pos ha c; positivity

theorem betaC_mul (ha : 0 < a) (hc : 0 ≤ c) : betaC a c * (uC a c + c) = a := by
  unfold betaC; have := uC_pos ha c; field_simp

theorem betaC_lt_one (ha : 0 < a) (hc : 0 < c) : betaC a c < 1 := by
  unfold betaC; have := a_lt_uC ha hc; rw [div_lt_one (by linarith)]; linarith

theorem one_sub_betaC_sq (ha : 0 < a) (hc : 0 ≤ c) :
    1 - betaC a c ^ 2 = 2 * c / (uC a c + c) := by
  have hu := uC_pos ha c
  have h2 := uC_sq a c
  unfold betaC
  field_simp
  nlinarith

theorem one_add_betaC_sq (ha : 0 < a) (hc : 0 ≤ c) :
    1 + betaC a c ^ 2 = 2 * uC a c / (uC a c + c) := by
  have hu := uC_pos ha c
  have h2 := uC_sq a c
  unfold betaC
  field_simp
  nlinarith

theorem continuous_fC (ha : 0 < a) (hc : 0 < c) : Continuous (fC a c) := by
  have hu := uC_pos ha c
  unfold fC
  refine Continuous.div (by fun_prop) (by fun_prop) fun θ => ?_
  have : 0 < a^2 * Real.cos θ ^ 2 + c^2 := by positivity
  positivity

/-- The Poisson-kernel form of the angular density. -/
theorem fC_eq_PK (ha : 0 < a) (hc : 0 < c) (θ : ℝ) :
    4 * π * fC a c θ =
      (PK (Complex.I * (betaC a c : ℝ)) θ + PK (Complex.I * ((-betaC a c : ℝ))) θ) / 2 - c / uC
        a c := by
  set β := betaC a c with hβ
  set u := uC a c with hu
  have hβ0 := betaC_pos ha hc.le
  have hβ1 := betaC_lt_one ha hc
  have hβ2 : β^2 < 1 := by nlinarith
  rw [PK_I_mul β β θ hβ2 (Or.inl rfl), PK_I_mul β (-β) θ hβ2 (Or.inr rfl)]
  have hu0 : 0 < u := uC_pos ha c
  have hu2 : u^2 = c^2 + a^2 := uC_sq a c
  have hm : β * (u + c) = a := betaC_mul ha hc.le
  have h1 := one_sub_betaC_sq ha hc.le
  have h2 := one_add_betaC_sq ha hc.le
  rw [← hβ, ← hu] at h1 h2
  have hs := Real.sin_sq_add_cos_sq θ
  have hDp : 0 < 1 - 2 * β * Real.sin θ + β^2 := by
    nlinarith [sq_nonneg (Real.sin θ - β), sq_nonneg (Real.cos θ)]
  have hDm : 0 < 1 - 2 * (-β) * Real.sin θ + β^2 := by
    nlinarith [sq_nonneg (Real.sin θ + β), sq_nonneg (Real.cos θ)]
  -- the product of the two denominators
  have hprod : (1 - 2 * β * Real.sin θ + β^2) * (1 - 2 * (-β) * Real.sin θ + β^2) =
      4 * (c^2 + a^2 * Real.cos θ ^ 2) / (u + c)^2 := by
    have e1 : (1 - 2 * β * Real.sin θ + β^2) * (1 - 2 * (-β) * Real.sin θ + β^2) =
        (1 - β^2)^2 + 4 * β^2 * Real.cos θ ^ 2 := by nlinarith
    rw [e1, h1]
    have hb : β = a / (u + c) := by rw [hβ]; rfl
    rw [hb]
    have : u + c ≠ 0 := by linarith
    field_simp
    ring
  have hsum : (1 - β^2) / (1 - 2 * β * Real.sin θ + β^2) +
      (1 - β^2) / (1 - 2 * (-β) * Real.sin θ + β^2) = 2 * c * u / (c^2 + a^2 * Real.cos θ ^ 2) := by
    rw [div_add_div _ _ hDp.ne' hDm.ne', hprod]
    have e2 : (1 - β^2) * (1 - 2 * (-β) * Real.sin θ + β^2) +
        (1 - 2 * β * Real.sin θ + β^2) * (1 - β^2) = 2 * (1 - β^2) * (1 + β^2) := by ring
    rw [e2, h1, h2]
    have : u + c ≠ 0 := by linarith
    have : 0 < c^2 + a^2 * Real.cos θ ^ 2 := by positivity
    field_simp
    ring
  rw [hsum]
  unfold fC
  rw [← hu]
  have : 0 < c^2 + a^2 * Real.cos θ ^ 2 := by positivity
  have : 0 < a^2 * Real.cos θ ^ 2 + c^2 := by positivity
  field_simp
  rw [hu2]
  linear_combination (a^2 * Real.cos θ ^ 2 + c^2) * a^2 * hs

/-- `a sin θ · ρ_c(a cos θ) = 2 fC θ` on `[0, π]`. -/
theorem sin_mul_rhoC (ha : 0 < a) (hc : 0 < c) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    |-(a * Real.sin θ)| * rhoC a c (a * Real.cos θ) = 2 * fC a c θ := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hsq : √(a^2 - (a * Real.cos θ)^2) = a * Real.sin θ := by
    rw [show a^2 - (a * Real.cos θ)^2 = (a * Real.sin θ)^2 by
      have := Real.sin_sq_add_cos_sq θ; nlinarith]
    exact Real.sqrt_sq (by positivity)
  have hu := uC_pos ha c
  rw [abs_neg, abs_of_nonneg (by positivity)]
  unfold rhoC fC
  rw [hsq]
  have : 0 < a^2 * Real.cos θ ^ 2 + c^2 := by positivity
  have : 0 < (a * Real.cos θ)^2 + c^2 := by positivity
  field_simp
  ring

theorem image_cos_Ioo (ha : 0 < a) :
    (fun θ => a * Real.cos θ) '' Ioo 0 π = Ioo (-a) a := by
  ext t
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have h1 : Real.cos θ < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
      simpa using this
    have h2 : -1 < Real.cos θ := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
      simpa using this
    constructor <;> nlinarith
  · intro ht
    have h1 : -1 < t / a := by rw [lt_div_iff₀ ha]; linarith [ht.1]
    have h2 : t / a < 1 := by rw [div_lt_one ha]; exact ht.2
    refine ⟨Real.arccos (t / a), ⟨Real.arccos_pos.mpr h2, Real.arccos_lt_pi.mpr h1⟩, ?_⟩
    simp only
    rw [Real.cos_arccos h1.le h2.le]
    field_simp

theorem injOn_cos_Ioo (ha : 0 < a) : InjOn (fun θ => a * Real.cos θ) (Ioo 0 π) := by
  intro x hx y hy hxy
  apply Real.injOn_cos (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
  simpa [ha.ne'] using hxy

theorem fC_two_pi_sub (a c θ : ℝ) : fC a c (2 * π - θ) = fC a c θ := by
  unfold fC
  rw [Real.sin_two_pi_sub, Real.cos_two_pi_sub, neg_sq]

/-- Change of variables `t = a cos θ` for the component density. -/
theorem integral_rhoC_eq (ha : 0 < a) (hc : 0 < c) (φ : ℝ → ℝ)
    (hφ : IntervalIntegrable (fun θ => φ (a * Real.cos θ) * fC a c θ) volume 0 π) :
    ∫ t in (-a)..a, φ t * rhoC a c t = ∫ θ in (0:ℝ)..2 * π, φ (a * Real.cos θ) * fC a c θ := by
  have hπ : (0:ℝ) ≤ π := Real.pi_pos.le
  -- step 1: the interval integral over `(-a, a)` as a set integral over the image of `(0, π)`
  have h1 : ∫ t in (-a)..a, φ t * rhoC a c t = ∫ t in Ioo (-a) a, φ t * rhoC a c t := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have h2 := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 π)
    (f := fun θ => a * Real.cos θ) (f' := fun θ => -(a * Real.sin θ)) measurableSet_Ioo
    (fun θ _ => by
      have := (Real.hasDerivAt_cos θ).const_mul a
      simpa [mul_neg] using this.hasDerivWithinAt) (injOn_cos_Ioo ha)
    (fun t => φ t * rhoC a c t)
  rw [image_cos_Ioo ha] at h2
  rw [h1, h2]
  -- step 2: the Jacobian identity on `(0, π)`
  have h3 : ∫ θ in Ioo 0 π, |-(a * Real.sin θ)| • (φ (a * Real.cos θ) * rhoC a c (a * Real.cos θ)) =
      ∫ θ in Ioo 0 π, 2 * (φ (a * Real.cos θ) * fC a c θ) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ hθ
    simp only [smul_eq_mul]
    rw [show |-(a * Real.sin θ)| * (φ (a * Real.cos θ) * rhoC a c (a * Real.cos θ)) =
      φ (a * Real.cos θ) * (|-(a * Real.sin θ)| * rhoC a c (a * Real.cos θ)) by ring,
      sin_mul_rhoC ha hc (Ioo_subset_Icc_self hθ)]
    ring
  rw [h3, integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπ]
  -- step 3: symmetry `θ ↦ 2π − θ`
  have hsym : ∫ θ in π..2 * π, φ (a * Real.cos θ) * fC a c θ =
      ∫ θ in (0:ℝ)..π, φ (a * Real.cos θ) * fC a c θ := by
    have := intervalIntegral.integral_comp_sub_left
      (fun θ => φ (a * Real.cos θ) * fC a c θ) (a := 0) (b := π) (2 * π)
    simp only [sub_zero, show 2 * π - π = π by ring] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Real.cos_two_pi_sub, fC_two_pi_sub]
  have hφ' : IntervalIntegrable (fun θ => φ (a * Real.cos θ) * fC a c θ) volume π (2 * π) := by
    have := hφ.comp_sub_left (2 * π)
    simp only [sub_zero, show 2 * π - π = π by ring] at this
    refine (this.symm.congr ?_)
    intro θ _
    simp only [Real.cos_two_pi_sub, fC_two_pi_sub]
  rw [← intervalIntegral.integral_add_adjacent_intervals hφ hφ', hsym]
  ring

end basic

end
end Zeta32.Analytic.EnergyI

end
