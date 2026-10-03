/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.Approx
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.JMNPeriodAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleArithmetic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Exact zeroth-order cutoff average used in the Section 3 one-step estimate. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

theorem OneStepAveraging.zetaMK_coord_of_ne_zero {β : ℝ} (I : Ingredients β)
    {m : ℕ} (_hm : 1 ≤ m) {k : ℤ} {t : ℝ}
    (hz : I.zetaMK m k t ≠ 0) :
    (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m ∈
      Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
  have hτ := I.tau_pos' m
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hnonneg : 0 ≤ I.zeta u := I.zeta_nonneg u
  have hpos : 0 < I.zeta u := by
    have hz' : I.zeta u ≠ 0 := by
      simpa [Ingredients.zetaMK, scaledCutoff, u] using hz
    exact lt_of_le_of_ne hnonneg (Ne.symm hz')
  by_contra hu
  have hind : indIcc (-(2 / 3 : ℝ)) (2 / 3) u = 0 := by
    unfold indIcc
    rw [Set.indicator_of_notMem hu]
  have hle := I.zeta_le_ind u
  rw [hind] at hle
  change I.zeta u ≤ 0 at hle
  linarith

/-- On `[0,4τ_m]`, a nonzero small cutoff can only have center `τ_m` or
`3τ_m`. -/
theorem OneStepAveraging.zetaMK_cell_centers {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {k : ℤ} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (4 * tau β I.Λ m))
    (hk : Odd k) (hz : I.zetaMK m k t ≠ 0) : k = 1 ∨ k = 3 := by
  have hτ := I.tau_pos' m
  have hcoord := OneStepAveraging.zetaMK_coord_of_ne_zero I hm hz
  have hcoord' : t / tau β I.Λ m - (k : ℝ) ∈
      Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    have heq : (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m =
        t / tau β I.Λ m - (k : ℝ) := by
      field_simp [ne_of_gt hτ]
    rw [heq] at hcoord
    exact hcoord
  have hratio : 0 ≤ t / tau β I.Λ m ∧ t / tau β I.Λ m ≤ 4 := by
    constructor
    · exact div_nonneg ht.1 hτ.le
    · exact (div_le_iff₀ hτ).2 ht.2
  have hkLo : (-1 : ℝ) < (k : ℝ) := by
    nlinarith [hratio.1, hcoord'.2]
  have hkHi : (k : ℝ) < 5 := by
    nlinarith [hratio.2, hcoord'.1]
  have hkLoI : -1 < k := by exact_mod_cast hkLo
  have hkHiI : k < 5 := by exact_mod_cast hkHi
  have hkBounds : 0 ≤ k ∧ k ≤ 4 := by
    constructor <;> omega
  rcases hk with ⟨n, rfl⟩
  have hn : 0 ≤ n ∧ n ≤ 1 := by omega
  rcases hn with ⟨hn0, hn1⟩
  interval_cases n <;> simp

/-- The integral of a scaled cutoff over a four-cell period is the prescribed
`9/10` mass of the original cutoff. -/
theorem OneStepAveraging.zetaMK_square_cell_integral {β : ℝ} (I : Ingredients β)
    {m : ℕ} (_hm : 1 ≤ m) (r : ℤ) (hr : r = 1 ∨ r = 3) :
    (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), I.zetaMK m r t ^ 2) =
      tau β I.Λ m * (9 / 10) := by
  have hτ := I.tau_pos' m
  have hfun : (fun t : ℝ => I.zetaMK m r t ^ 2) =
      fun t => I.zeta (t / tau β I.Λ m - (r : ℝ)) ^ 2 := by
    funext t
    unfold Ingredients.zetaMK scaledCutoff
    congr 1
    field_simp [ne_of_gt hτ]
  rw [hfun]
  let g : ℝ → ℝ := fun u => I.zeta u ^ 2
  let f : ℝ → ℝ := fun t => t / tau β I.Λ m - (r : ℝ)
  have hf : ∀ t ∈ Set.uIcc (0 : ℝ) (4 * tau β I.Λ m),
      HasDerivAt f (tau β I.Λ m)⁻¹ t := by
    intro t _
    dsimp [f]
    have h := (hasDerivAt_id t).div_const (tau β I.Λ m)
    simpa [div_eq_mul_inv, mul_comm] using h.sub_const (r : ℝ)
  have hg : Continuous g := by
    dsimp [g]
    exact I.zeta_smooth.continuous.pow 2
  have hfcont : Continuous f := by
    dsimp [f]
    exact (continuous_id.div_const (tau β I.Λ m)).sub continuous_const
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (f := f) (f' := fun _ => (tau β I.Λ m)⁻¹) (g := g)
    (a := (0 : ℝ)) (b := 4 * tau β I.Λ m) hf
    continuousOn_const hg
  have hf0 : f 0 = -(r : ℝ) := by simp [f]
  have hf1 : f (4 * tau β I.Λ m) = 4 - (r : ℝ) := by
    dsimp [f]
    field_simp [ne_of_gt hτ]
  rw [hf0, hf1] at hchange
  have hsupport : Function.support g ⊆ Set.Ioc (-(r : ℝ)) (4 - (r : ℝ)) := by
    intro u hu
    have hgu : g u ≠ 0 := Function.mem_support.mp hu
    have hz : I.zeta u ≠ 0 := by
      intro hzero
      apply hgu
      simp [g, hzero]
    have hcore : u ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
      by_contra hnot
      have hind : indIcc (-(2 / 3 : ℝ)) (2 / 3) u = 0 := by
        unfold indIcc
        rw [Set.indicator_of_notMem hnot]
      have hle := I.zeta_le_ind u
      rw [hind] at hle
      have hnonneg := I.zeta_nonneg u
      have hzero : I.zeta u = 0 := le_antisymm hle hnonneg
      exact hz hzero
    rcases hr with hr1 | hr3
    · subst r
      have hbound : u ∈ Set.Ioc (-1 : ℝ) 3 := by
        constructor
        · linarith [hcore.1]
        · linarith [hcore.2]
      convert hbound using 1; norm_num
    · subst r
      have hbound : u ∈ Set.Ioc (-3 : ℝ) 1 := by
        constructor
        · linarith [hcore.1]
        · linarith [hcore.2]
      convert hbound using 1; norm_num
  have hwhole := intervalIntegral.integral_eq_integral_of_support_subset
    (μ := volume) hsupport
  have hperiodInt :
      (∫ u in (-(r : ℝ))..(4 - (r : ℝ)), g u) = 9 / 10 := by
    calc
      (∫ u in (-(r : ℝ))..(4 - (r : ℝ)), g u) = ∫ u, g u := hwhole
      _ = 9 / 10 := by simpa [g] using I.zeta_sq_integral
  have hτne : tau β I.Λ m ≠ 0 := ne_of_gt hτ
  have hscaleInt :
      (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), g (f t)) =
        tau β I.Λ m * (∫ u in (-(r : ℝ))..(4 - (r : ℝ)), g u) := by
    have hchange' :
        (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), g (f t)) *
            (tau β I.Λ m)⁻¹ =
          ∫ u in (-(r : ℝ))..(4 - (r : ℝ)), g u := by
      calc
        (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), g (f t)) *
            (tau β I.Λ m)⁻¹ =
            ∫ t in (0 : ℝ)..(4 * tau β I.Λ m), g (f t) *
              (tau β I.Λ m)⁻¹ := by
                exact (intervalIntegral.integral_mul_const _ _).symm
        _ = ∫ u in (-(r : ℝ))..(4 - (r : ℝ)), g u := by
          simpa only [Function.comp_apply] using hchange
    calc
      (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), g (f t)) =
          ((∫ t in (0 : ℝ)..(4 * tau β I.Λ m), g (f t)) *
            (tau β I.Λ m)⁻¹) * tau β I.Λ m := by
              field_simp [hτne]
      _ = (∫ u in (-(r : ℝ))..(4 - (r : ℝ)), g u) * tau β I.Λ m := by
        rw [hchange']
      _ = _ := by ring
  calc
    _ = ∫ t in (0 : ℝ)..(4 * tau β I.Λ m), g (f t) := by rfl
    _ = tau β I.Λ m * (9 / 10) := by rw [hscaleInt, hperiodInt]

/-- Diagonal projector onto the second coordinate for the first shear mode. -/
def OneStepAveraging.shearModeOne : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
/-- Diagonal projector onto the first coordinate for the third shear mode. -/
def OneStepAveraging.shearModeThree : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- During a four-cell period, the order-zero shear flux has only the two
modes centered at cells one and three. -/
theorem OneStepAveraging.jMN_zero_two_mode_formula {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (4 * tau β I.Λ m)) :
    I.jMN κ m 0 t =
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) •
        (I.zetaMK m 1 t ^ 2 • OneStepAveraging.shearModeOne +
          I.zetaMK m 3 t ^ 2 • OneStepAveraging.shearModeThree) := by
  classical
  let k1 : {k : ℤ // Odd k} := ⟨1, ⟨0, by norm_num⟩⟩
  let k3 : {k : ℤ // Odd k} := ⟨3, ⟨1, by norm_num⟩⟩
  let S : Finset {k : ℤ // Odd k} := {k1, k3}
  let term : {k : ℤ // Odd k} → Matrix (Fin 2) (Fin 2) ℝ := fun k =>
    (I.zetaMK m k t * iteratedDeriv 0 (I.zetaMK m k) t) •
      ((if (k : ℤ) % 4 = 1 then OneStepAveraging.shearModeOne else 0) +
        (if (k : ℤ) % 4 = 3 then OneStepAveraging.shearModeThree else 0))
  have hsum : (∑' k : {k : ℤ // Odd k}, term k) =
      ∑ k ∈ S, term k := by
    apply tsum_eq_sum
    intro k hk
    have hzero : I.zetaMK m k t = 0 := by
      by_contra hne
      rcases OneStepAveraging.zetaMK_cell_centers I hm ht k.property hne with h1 | h3
      · apply hk
        have heq : k = k1 := Subtype.ext h1
        simp [S, heq]
      · apply hk
        have heq : k = k3 := Subtype.ext h3
        simp [S, heq]
    simp [term, hzero]
  have hsum' :
      (∑' k : {k : ℤ // Odd k},
        (I.zetaMK m k t * iteratedDeriv 0 (I.zetaMK m k) t) •
          ((if (k : ℤ) % 4 = 1 then !![0, 0; 0, 1] else 0) +
            (if (k : ℤ) % 4 = 3 then !![1, 0; 0, 0] else 0))) =
        I.zetaMK m 1 t ^ 2 • OneStepAveraging.shearModeOne +
          I.zetaMK m 3 t ^ 2 • OneStepAveraging.shearModeThree := by
    calc
      _ = ∑ k ∈ S, term k := by simpa [term, OneStepAveraging.shearModeOne,
          OneStepAveraging.shearModeThree] using hsum
      _ = term k1 + term k3 := by
        rw [show S = {k1, k3} by rfl, Finset.sum_pair (by decide)]
      _ = _ := by
        simp [term, OneStepAveraging.shearModeOne, OneStepAveraging.shearModeThree, k1, k3]
        ring_nf
        trivial
  unfold Ingredients.jMN
  rw [hsum']
  simp

/-- Exact period average of the order-zero oscillatory flux. -/
theorem jMN_zero_average_eq {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) :
    timeAvgMat (I.jMN κ m 0) =
      ((9 * Real.pi ^ 2 / 20) * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (4 * tau β I.Λ m)) :=
    OneStepAveraging.jMN_zero_two_mode_formula I hm κ t ht
  have hτ := I.tau_pos' m
  have hcell1 := OneStepAveraging.zetaMK_square_cell_integral I hm (1 : ℤ) (Or.inl rfl)
  have hcell3 := OneStepAveraging.zetaMK_square_cell_integral I hm (3 : ℤ) (Or.inr rfl)
  ext i j
  change (∫ t in (0 : ℝ)..1, I.jMN κ m 0 t i j) = _
  rw [jMN_average_eq_period_average I hm κ i j]
  have hInt :
      (∫ t in (0 : ℝ)..(4 * tau β I.Λ m), I.jMN κ m 0 t i j) =
        ∫ t in (0 : ℝ)..(4 * tau β I.Λ m),
          ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) •
            (I.zetaMK m 1 t ^ 2 • OneStepAveraging.shearModeOne +
              I.zetaMK m 3 t ^ 2 • OneStepAveraging.shearModeThree)) i j := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) (4 * tau β I.Λ m) := by
      have h0P : (0 : ℝ) ≤ 4 * tau β I.Λ m := by linarith [hτ]
      simpa [Set.uIcc_of_le h0P] using ht
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) (hpoint t ht')
  rw [hInt]
  fin_cases i
  · fin_cases j
    · simp [Matrix.smul_apply, smul_eq_mul, OneStepAveraging.shearModeOne,
        OneStepAveraging.shearModeThree,
        intervalIntegral.integral_const_mul, hcell3]
      field_simp [ne_of_gt hτ]
      ring
    · simp [Matrix.smul_apply, smul_eq_mul, OneStepAveraging.shearModeOne,
        OneStepAveraging.shearModeThree]
  · fin_cases j
    · simp [Matrix.smul_apply, smul_eq_mul, OneStepAveraging.shearModeOne,
        OneStepAveraging.shearModeThree]
    · simp [Matrix.smul_apply, smul_eq_mul, OneStepAveraging.shearModeOne,
        OneStepAveraging.shearModeThree,
        intervalIntegral.integral_const_mul, hcell1]
      field_simp [ne_of_gt hτ]
      ring

theorem OneStepAveraging.expShift_integrableOn_Iic {ρ t : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => Real.exp (ρ * (s - t))) (Set.Iic t) := by
  have hbase := integrableOn_exp_mul_Iic hρ t
  have heq : (fun s : ℝ => Real.exp (ρ * (s - t))) =
      fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) := by
    funext s
    rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring, Real.exp_add]
    ring
  rw [heq]
  exact hbase.const_mul _

theorem OneStepAveraging.expShift_integral_Iic {ρ t : ℝ} (hρ : 0 < ρ) :
    (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) = ρ⁻¹ := by
  have hcancel : Real.exp (-ρ * t) * Real.exp (ρ * t) = 1 := by
    rw [← Real.exp_add, show -ρ * t + ρ * t = 0 by ring, Real.exp_zero]
  calc
    (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) =
        Real.exp (-ρ * t) * (∫ s in Set.Iic t, Real.exp (ρ * s)) := by
          rw [show (fun s : ℝ => Real.exp (ρ * (s - t))) =
            fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) by
              funext s
              rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring, Real.exp_add]
              ring]
          rw [integral_const_mul]
    _ = Real.exp (-ρ * t) * (Real.exp (ρ * t) / ρ) := by
          rw [integral_exp_mul_Iic hρ t]
    _ = ρ⁻¹ := by
          rw [div_eq_mul_inv, ← mul_assoc, hcancel]
          simp

theorem OneStepAveraging.hatZeta_memory_integrable {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {ρ t : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => I.hatZetaML m l s *
      Real.exp (ρ * (s - t))) (Set.Iic t) := by
  have hExp := OneStepAveraging.expShift_integrableOn_Iic (ρ := ρ) (t := t) hρ
  have hcutcont : Continuous (I.hatZetaML m l) := by
    unfold Ingredients.hatZetaML shiftCutoff
    exact (I.hatZeta_smooth m).continuous.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => I.hatZetaML m l s * Real.exp (ρ * (s - t)))
      (volume.restrict (Set.Iic t)) := by
    exact (hcutcont.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).aestronglyMeasurable.restrict
  apply hExp.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (hatZetaML_mem_Icc I hm l s).1,
    abs_of_pos (Real.exp_pos _)]
  calc
    I.hatZetaML m l s * Real.exp (ρ * (s - t)) ≤
        1 * Real.exp (ρ * (s - t)) :=
      mul_le_mul_of_nonneg_right (hatZetaML_mem_Icc I hm l s).2
        (Real.exp_nonneg _)
    _ = Real.exp (ρ * (s - t)) := by ring

theorem OneStepAveraging.hatZeta_memory_bounds {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {ρ t : ℝ} (hρ : 0 < ρ) :
    0 ≤ (∫ s in Set.Iic t, I.hatZetaML m l s * Real.exp (ρ * (s - t))) ∧
    (∫ s in Set.Iic t, I.hatZetaML m l s * Real.exp (ρ * (s - t))) ≤ ρ⁻¹ := by
  have hExpInt := OneStepAveraging.expShift_integrableOn_Iic (ρ := ρ) (t := t) hρ
  have hCutInt := OneStepAveraging.hatZeta_memory_integrable I hm l (ρ := ρ) (t := t) hρ
  have hnonneg : ∀ s ∈ Set.Iic t,
      0 ≤ I.hatZetaML m l s * Real.exp (ρ * (s - t)) := by
    intro s hs
    exact mul_nonneg (hatZetaML_mem_Icc I hm l s).1 (Real.exp_nonneg _)
  have hmono :
      (∫ s in Set.Iic t, I.hatZetaML m l s * Real.exp (ρ * (s - t))) ≤
        ∫ s in Set.Iic t, Real.exp (ρ * (s - t)) := by
    apply setIntegral_mono_on hCutInt hExpInt measurableSet_Iic
    intro s hs
    calc
      I.hatZetaML m l s * Real.exp (ρ * (s - t)) ≤
          1 * Real.exp (ρ * (s - t)) :=
        mul_le_mul_of_nonneg_right (hatZetaML_mem_Icc I hm l s).2
          (Real.exp_nonneg _)
      _ = Real.exp (ρ * (s - t)) := by ring
  constructor
  · exact setIntegral_nonneg measurableSet_Iic hnonneg
  · rw [OneStepAveraging.expShift_integral_Iic hρ] at hmono
    exact hmono

theorem OneStepAveraging.hatZetaML_eq_one_on_core {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (T P t : ℝ)
    (ht : t ∈ Set.Icc ((l - 1 / 2) * T + 2 * P)
      ((l + 1 / 2) * T - 2 * P))
    (hT : T = tauPP β I.Λ m) (hP : P = tauP β I.Λ m) :
    I.hatZetaML m l t = 1 := by
  have hPpos : 0 < P := by
    rw [hP]
    exact Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hmemLow : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m +
      2 * tauP β I.Λ m) ((l + 1 / 2) * tauPP β I.Λ m -
      2 * tauP β I.Λ m) := by
    simpa [hT, hP] using ht
  have hmemUp : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m +
      tauP β I.Λ m) ((l + 1 / 2) * tauPP β I.Λ m -
      tauP β I.Λ m) := by
    constructor <;> linarith [hmemLow.1, hmemLow.2]
  have hlow := I.hatZeta_ge m hm l t
  have hupp := I.hatZeta_le m hm l t
  have hlow' : 1 ≤ I.hatZetaML m l t := by
    have hindicator : indIcc ((l - 1 / 2) * tauPP β I.Λ m +
        2 * tauP β I.Λ m) ((l + 1 / 2) * tauPP β I.Λ m -
        2 * tauP β I.Λ m) t = 1 := by
      unfold indIcc
      rw [Set.indicator_of_mem hmemLow]
    rw [hindicator] at hlow
    change 1 ≤ I.hatZetaML m l t at hlow
    exact hlow
  have hupp' : I.hatZetaML m l t ≤ 1 := by
    have hindicator : indIcc ((l - 1 / 2) * tauPP β I.Λ m +
        tauP β I.Λ m) ((l + 1 / 2) * tauPP β I.Λ m -
        tauP β I.Λ m) t = 1 := by
      unfold indIcc
      rw [Set.indicator_of_mem hmemUp]
    rw [hindicator] at hupp
    change I.hatZetaML m l t ≤ 1 at hupp
    exact hupp
  exact le_antisymm hupp' hlow'

theorem OneStepAveraging.LMN_zero_nonneg {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (t : ℝ) :
    0 ≤ I.LMN κ m 0 t := by
  classical
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let S := (I.hatZetaML_support_finite hm t).toFinset
  let term : ℤ → ℝ := fun l => I.hatZetaML m l t *
    ∫ s in Set.Iic t, I.hatZetaML m l s * Real.exp (ρ * (s - t))
  have hsumRaw : I.LMN κ m 0 t = ∑ l ∈ S,
      I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s *
          (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ 0 *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)) := by
    unfold Ingredients.LMN
    apply tsum_eq_sum
    intro l hl
    have hz : I.hatZetaML m l t = 0 := by
      by_contra hne
      exact hl ((Set.Finite.mem_toFinset _).2 hne)
    simp [hz]
  have hsum : I.LMN κ m 0 t = ∑ l ∈ S, term l := by
    simpa [term, ρ, pow_zero, mul_one] using hsumRaw
  rw [hsum]
  apply Finset.sum_nonneg
  intro l hl
  have hρ : 0 < 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 := by
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    positivity
  have hmem := OneStepAveraging.hatZeta_memory_bounds I hm l (ρ := 4 * Real.pi ^ 2 * κ /
    epsilon β I.Λ m ^ 2) (t := t) hρ
  exact mul_nonneg (hatZetaML_mem_Icc I hm l t).1 hmem.1

theorem OneStepAveraging.LMN_zero_le_inv {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (t : ℝ) :
    I.LMN κ m 0 t ≤ (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ := by
  classical
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let S := (I.hatZetaML_support_finite hm t).toFinset
  let term : ℤ → ℝ := fun l => I.hatZetaML m l t *
    ∫ s in Set.Iic t, I.hatZetaML m l s * Real.exp (ρ * (s - t))
  have hsumRaw : I.LMN κ m 0 t = ∑ l ∈ S,
      I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s *
          (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ 0 *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)) := by
    unfold Ingredients.LMN
    apply tsum_eq_sum
    intro l hl
    have hz : I.hatZetaML m l t = 0 := by
      by_contra hne
      exact hl ((Set.Finite.mem_toFinset _).2 hne)
    simp [hz]
  have hsum : I.LMN κ m 0 t = ∑ l ∈ S, term l := by
    simpa [term, ρ, pow_zero, mul_one] using hsumRaw
  have hweight : (∑ l ∈ S, I.hatZetaML m l t) ≤ 1 := by
    calc
      (∑ l ∈ S, I.hatZetaML m l t) ≤ ∑ l ∈ S, I.hatXiML m l t :=
        Finset.sum_le_sum (fun l _ => hatZetaML_le_hatXiML I hm l t)
      _ ≤ ∑' l : ℤ, I.hatXiML m l t :=
        (summable_of_hasFiniteSupport (I.hatXiML_support_finite hm t)).sum_le_tsum S
          (fun l _ => (Infra.Ingredients.hatXiML_mem_Icc I hm l t).1)
      _ = 1 := Infra.Ingredients.hatXiML_partition I hm t
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    positivity
  rw [hsum]
  calc
    (∑ l ∈ S, term l) ≤ ∑ l ∈ S, I.hatZetaML m l t * ρ⁻¹ := by
      apply Finset.sum_le_sum
      intro l hl
      dsimp [term]
      exact mul_le_mul_of_nonneg_left
        (OneStepAveraging.hatZeta_memory_bounds I hm l (ρ := ρ) (t := t) hρ).2
        (hatZetaML_mem_Icc I hm l t).1
    _ = (∑ l ∈ S, I.hatZetaML m l t) * ρ⁻¹ := by rw [Finset.sum_mul]
    _ ≤ 1 * ρ⁻¹ := by
      exact mul_le_mul_of_nonneg_right hweight (inv_nonneg.mpr hρ.le)
    _ = ρ⁻¹ := by ring

theorem OneStepAveraging.LMN_zero_ge_core {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (T P t : ℝ) (hT : T = tauPP β I.Λ m) (hP : P = tauP β I.Λ m)
    (ht : t ∈ Set.Icc (-(T / 2) + 3 * P) (T / 2 - 2 * P)) :
    (1 - Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * P)) /
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) ≤ I.LMN κ m 0 t := by
  classical
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let S := (I.hatZetaML_support_finite hm t).toFinset
  let term : ℤ → ℝ := fun l => I.hatZetaML m l t *
    ∫ s in Set.Iic t, I.hatZetaML m l s * Real.exp (ρ * (s - t))
  have hTpp : T = tauPP β I.Λ m := hT
  have hPp : P = tauP β I.Λ m := hP
  have hcore : t ∈ Set.Icc (-(T / 2) + 2 * P) (T / 2 - 2 * P) := by
    have hPpos : 0 < P := by
      rw [hP]
      exact Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    exact ⟨by linarith [ht.1], ht.2⟩
  have hhatT : I.hatZetaML m 0 t = 1 := by
    have hcore' : t ∈ Set.Icc ((((0 : ℤ) : ℝ) - (1 / 2 : ℝ)) * T + 2 * P)
        ((((0 : ℤ) : ℝ) + (1 / 2 : ℝ)) * T - 2 * P) := by
      constructor
      · have hEq : ((((0 : ℤ) : ℝ) - (1 / 2 : ℝ)) * T + 2 * P) =
            -(T / 2) + 2 * P := by norm_num; ring
        rw [hEq]
        exact hcore.1
      · have hEq : ((((0 : ℤ) : ℝ) + (1 / 2 : ℝ)) * T - 2 * P) =
            T / 2 - 2 * P := by norm_num; ring
        rw [hEq]
        exact hcore.2
    exact OneStepAveraging.hatZetaML_eq_one_on_core I hm (0 : ℤ) T P t hcore' hT hP
  have hsumRaw : I.LMN κ m 0 t = ∑ l ∈ S,
      I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s *
          (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ 0 *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)) := by
    unfold Ingredients.LMN
    apply tsum_eq_sum
    intro l hl
    have hz : I.hatZetaML m l t = 0 := by
      by_contra hne
      exact hl ((Set.Finite.mem_toFinset _).2 hne)
    simp [hz]
  have hsum : I.LMN κ m 0 t = ∑ l ∈ S, term l := by
    simpa [term, ρ, pow_zero, mul_one] using hsumRaw
  have htermNonneg : ∀ l ∈ S, 0 ≤ term l := by
    intro l hl
    dsimp [term]
    have hρ : 0 < ρ := by
      dsimp [ρ]
      have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := m)
      positivity
    exact mul_nonneg (hatZetaML_mem_Icc I hm l t).1
      (OneStepAveraging.hatZeta_memory_bounds I hm l (ρ := ρ) (t := t) hρ).1
  have hmem0 : 0 ∈ S := by
    apply (Set.Finite.mem_toFinset _).2
    have hne : I.hatZetaML m 0 t ≠ 0 := by rw [hhatT]; norm_num
    exact hne
  have hsumlower : term 0 ≤ ∑ l ∈ S, term l :=
    Finset.single_le_sum htermNonneg hmem0
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    positivity
  have hinterval : ∀ s ∈ Set.Ioc (t - P) t, I.hatZetaML m 0 s = 1 := by
    intro s hs
    have hslo : -(T / 2) + 2 * P ≤ s := by nlinarith [ht.1, hs.1]
    have hshi : s ≤ T / 2 - 2 * P := by linarith [ht.2, hs.2]
    have hsCore : s ∈ Set.Icc (-(T / 2) + 2 * P) (T / 2 - 2 * P) := ⟨hslo, hshi⟩
    have hsCore' : s ∈ Set.Icc ((((0 : ℤ) : ℝ) - (1 / 2 : ℝ)) * T + 2 * P)
        ((((0 : ℤ) : ℝ) + (1 / 2 : ℝ)) * T - 2 * P) := by
      constructor
      · have hEq : ((((0 : ℤ) : ℝ) - (1 / 2 : ℝ)) * T + 2 * P) =
            -(T / 2) + 2 * P := by norm_num; ring
        rw [hEq]
        exact hsCore.1
      · have hEq : ((((0 : ℤ) : ℝ) + (1 / 2 : ℝ)) * T - 2 * P) =
            T / 2 - 2 * P := by norm_num; ring
        rw [hEq]
        exact hsCore.2
    exact OneStepAveraging.hatZetaML_eq_one_on_core I hm (0 : ℤ) T P s hsCore' hT hP
  have hcutInt := OneStepAveraging.hatZeta_memory_integrable I hm 0 (ρ := ρ) (t := t) hρ
  have hkernelInt := OneStepAveraging.expShift_integrableOn_Iic (ρ := ρ) (t := t) hρ
  have hseg : Set.Ioc (t - P) t ⊆ Set.Iic t := Set.Ioc_subset_Iic_self
  have hmemseg :
      (∫ s in Set.Ioc (t - P) t,
        I.hatZetaML m 0 s * Real.exp (ρ * (s - t))) ≤
      (∫ s in Set.Iic t,
        I.hatZetaML m 0 s * Real.exp (ρ * (s - t))) :=
    setIntegral_mono_set hcutInt
      (ae_of_all _ (fun s => mul_nonneg
        (hatZetaML_mem_Icc I hm 0 s).1 (Real.exp_nonneg _)))
      (Filter.Eventually.of_forall hseg)
  have hseg_eq :
      (∫ s in Set.Ioc (t - P) t,
        I.hatZetaML m 0 s * Real.exp (ρ * (s - t))) =
      ∫ s in Set.Ioc (t - P) t, Real.exp (ρ * (s - t)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change I.hatZetaML m 0 s * Real.exp (ρ * (s - t)) = _
    rw [hinterval s hs, one_mul]
  have hsegInt :
      (∫ s in Set.Ioc (t - P) t, Real.exp (ρ * (s - t))) =
        (1 - Real.exp (-ρ * P)) / ρ := by
    have hP0 : 0 < P := by
      rw [hP]
      exact Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hle : t - P ≤ t := by linarith
    have hIoc : (∫ s in Set.Ioc (t - P) t, Real.exp (ρ * (s - t))) =
        ∫ s in (t - P)..t, Real.exp (ρ * (s - t)) := by
      symm
      exact intervalIntegral.integral_of_le hle
    rw [hIoc]
    let f : ℝ → ℝ := fun s => ρ * (s - t)
    have hf : ∀ s ∈ Set.uIcc (t - P) t, HasDerivAt f ρ s := by
      intro s _
      dsimp [f]
      simpa using (hasDerivAt_id s).sub_const t |>.const_mul ρ
    have hchange := intervalIntegral.integral_comp_mul_deriv
      (f := f) (f' := fun _ => ρ) (g := Real.exp)
      (a := t - P) (b := t) hf continuousOn_const Real.continuous_exp
    have hf0 : f (t - P) = -ρ * P := by dsimp [f]; ring
    have hf1 : f t = 0 := by dsimp [f]; ring
    have hprimitive : (∫ u in (-ρ * P)..0, Real.exp u) =
        1 - Real.exp (-ρ * P) := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := -ρ * P) (b := (0 : ℝ))
        (f := Real.exp) (f' := Real.exp)
        (fun u _ => Real.hasDerivAt_exp u)
        (Real.continuous_exp.intervalIntegrable _ _)
      simpa only [Real.exp_zero, sub_zero] using h
    rw [hf0, hf1, hprimitive] at hchange
    have hmul :
        (∫ s in (t - P)..t, Real.exp (ρ * (s - t))) * ρ =
          1 - Real.exp (-ρ * P) := by
      simpa [f] using hchange
    rw [← hmul]
    field_simp [ne_of_gt hρ]
  have hmem0lower :
      (1 - Real.exp (-ρ * P)) / ρ ≤
        ∫ s in Set.Iic t, I.hatZetaML m 0 s * Real.exp (ρ * (s - t)) := by
    calc
      (1 - Real.exp (-ρ * P)) / ρ =
          ∫ s in Set.Ioc (t - P) t,
            I.hatZetaML m 0 s * Real.exp (ρ * (s - t)) :=
              hsegInt.symm.trans hseg_eq.symm
      _ ≤ _ := hmemseg
  have hterm : term 0 = ∫ s in Set.Iic t,
      I.hatZetaML m 0 s * Real.exp (ρ * (s - t)) := by
    simp [term, hhatT]
  change (1 - Real.exp (-ρ * P)) / ρ ≤ I.LMN κ m 0 t
  calc
    (1 - Real.exp (-ρ * P)) / ρ ≤
        ∫ s in Set.Iic t, I.hatZetaML m 0 s * Real.exp (ρ * (s - t)) := hmem0lower
    _ = term 0 := hterm.symm
    _ ≤ ∑ l ∈ S, term l := hsumlower
    _ = I.LMN κ m 0 t := hsum.symm

/-- Period averaging bounds the zeroth memory coefficient from above by the
full relaxation scale and from below by the contribution of the plateau. -/
theorem LMN_zero_unit_average_bounds {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) :
    let T := tauPP β I.Λ m
    let P := tauP β I.Λ m
    let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
    0 ≤ (∫ t in (0 : ℝ)..1, I.LMN κ m 0 t) ∧
      (∫ t in (0 : ℝ)..1, I.LMN κ m 0 t) ≤ ρ⁻¹ ∧
      (((1 / T) * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
        ∫ t in (0 : ℝ)..1, I.LMN κ m 0 t) := by
  classical
  dsimp only
  let T := tauPP β I.Λ m
  let P := tauP β I.Λ m
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let f : ℝ → ℝ := I.LMN κ m 0
  have hT : 0 < T := by dsimp [T]; exact I.tauPP_pos' m
  have hP : 0 < P := by
    dsimp [P]
    exact Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    positivity
  have hfactor : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    have heps := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
    have hpow : 0 < epsilon β I.Λ (m - 1) ^ (-delta β) :=
      Real.rpow_pos_of_pos heps _
    have hceil : 1 ≤ ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ :=
      Nat.ceil_pos.mpr hpow
    exact_mod_cast (show 5 ≤ 4 * ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ + 1 by omega)
  have hTP : 5 * P ≤ T := by
    have hscale := Infra.Ingredients.tauPP_eq_cellFactor_mul_tauP
      (β := β) (Λ := I.Λ) hm
    have hfactorReal : (5 : ℝ) ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
      exact_mod_cast hfactor
    dsimp [T, P]
    rw [hscale]
    nlinarith [hP.le]
  have hcont : Continuous f := by
    dsimp [f]
    exact (LMN_contDiff I hm hκ 0).continuous
  have hnonneg (t : ℝ) : 0 ≤ f t := by
    dsimp [f]
    exact OneStepAveraging.LMN_zero_nonneg I hm κ hκ t
  have hup (t : ℝ) : f t ≤ ρ⁻¹ := by
    dsimp [f, ρ]
    exact OneStepAveraging.LMN_zero_le_inv I hm κ hκ t
  have hperiod : Function.Periodic f T := by
    intro t
    dsimp [f, T]
    exact LMN_periodic I κ m 0 t
  obtain ⟨n, hrecipN⟩ := Infra.Ingredients.tauPP_reciprocal_multiple_four
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
  let N : ℕ := 4 * n
  have hNperiod : (N : ℝ) * T = 1 := by
    have hrecip : 1 / T = (N : ℝ) := by
      dsimp [T, N]
      exact_mod_cast hrecipN
    have hone : 1 = (N : ℝ) * T := (div_eq_iff hT.ne').mp hrecip
    linarith
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hunit := intervalIntegral_unit_eq_period_mul hperiod hcont hNperiod
  have hcenter : (∫ t in (-(T / 2))..(T / 2), f t) =
      ∫ t in (0 : ℝ)..T, f t := by
    have h := hperiod.intervalIntegral_add_eq (-(T / 2)) 0
    have hend : -(T / 2) + T = T / 2 := by ring
    rw [hend] at h
    simpa only [zero_add] using h
  let lo := -(T / 2) + 3 * P
  let hi := T / 2 - 2 * P
  have hlo : -(T / 2) ≤ lo := by dsimp [lo]; linarith
  have hhi : hi ≤ T / 2 := by dsimp [hi]; linarith
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hwholeInt : IntervalIntegrable f volume (-(T / 2)) (T / 2) :=
    hcont.intervalIntegrable _ _
  have hleftInt : IntervalIntegrable f volume (-(T / 2)) lo :=
    hcont.intervalIntegrable _ _
  have hcoreInt : IntervalIntegrable f volume lo hi := hcont.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable f volume hi (T / 2) := hcont.intervalIntegrable _ _
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals hleftInt hcoreInt
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals
    (hleftInt.trans hcoreInt) hrightInt
  have hleftNonneg : 0 ≤ (∫ t in (-(T / 2))..lo, f t) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t _
    exact hnonneg t
  have hrightNonneg : 0 ≤ (∫ t in hi..(T / 2), f t) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t _
    exact hnonneg t
  have hcorePoint (t : ℝ) (ht : t ∈ Set.uIcc lo hi) :
      (1 - Real.exp (-ρ * P)) / ρ ≤ f t := by
    have ht' : t ∈ Set.Icc lo hi := by
      simpa [Set.uIcc_of_le hlohi] using ht
    dsimp [f, lo, hi]
    exact OneStepAveraging.LMN_zero_ge_core I hm κ hκ T P t rfl rfl ht'
  have hcoreLower : (hi - lo) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
      (∫ t in lo..hi, f t) := by
    have hmono := intervalIntegral.integral_mono_on hlohi intervalIntegrable_const hcoreInt
      (fun t ht => hcorePoint t (by
        simpa [Set.uIcc_of_le hlohi] using ht))
    calc
      (hi - lo) * ((1 - Real.exp (-ρ * P)) / ρ) =
          ∫ t in lo..hi, ((1 - Real.exp (-ρ * P)) / ρ) := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
      _ ≤ _ := hmono
  have hcenterLower :
      (T - 5 * P) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
        (∫ t in (-(T / 2))..(T / 2), f t) := by
    have hlength : hi - lo = T - 5 * P := by dsimp [hi, lo]; ring
    calc
      (T - 5 * P) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
          ∫ t in lo..hi, f t := by rw [← hlength]; exact hcoreLower
      _ ≤ (∫ t in (-(T / 2))..lo, f t) +
            (∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t) := by
          have hr : (∫ t in lo..hi, f t) ≤
              (∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t) :=
            le_add_of_nonneg_right hrightNonneg
          have hl : (∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t) ≤
              (∫ t in (-(T / 2))..lo, f t) +
                ((∫ t in lo..hi, f t) + (∫ t in hi..(T / 2), f t)) :=
            le_add_of_nonneg_left hleftNonneg
          linarith
      _ = ∫ t in (-(T / 2))..(T / 2), f t := by
          rw [← hsplitRight, ← hsplitLeft]
  have hcenterUpper :
      (∫ t in (-(T / 2))..(T / 2), f t) ≤ T * ρ⁻¹ := by
    have hmono := intervalIntegral.integral_mono_on (by linarith [hT]) hwholeInt
      intervalIntegrable_const (fun t _ => hup t)
    calc
      (∫ t in (-(T / 2))..(T / 2), f t) ≤
          ∫ t in (-(T / 2))..(T / 2), ρ⁻¹ := hmono
      _ = T * ρ⁻¹ := by simp [intervalIntegral.integral_const, smul_eq_mul]
  have hperiodUpper : (∫ t in (0 : ℝ)..T, f t) ≤ T * ρ⁻¹ := by
    rw [← hcenter]
    exact hcenterUpper
  have hunitUpper : (∫ t in (0 : ℝ)..1, f t) ≤ ρ⁻¹ := by
    rw [hunit]
    calc
      (N : ℝ) * (∫ t in (0 : ℝ)..T, f t) ≤ (N : ℝ) * (T * ρ⁻¹) :=
        mul_le_mul_of_nonneg_left hperiodUpper hNnonneg
      _ = ρ⁻¹ := by rw [← mul_assoc, hNperiod]; ring
  have hN_eq : (N : ℝ) = 1 / T := by
    apply (eq_div_iff hT.ne').2
    nlinarith [hNperiod]
  have hunitLower :
      ((1 / T) * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ) ≤
        (∫ t in (0 : ℝ)..1, f t) := by
    calc
      ((1 / T) * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ) =
          (N : ℝ) * ((T - 5 * P) * ((1 - Real.exp (-ρ * P)) / ρ)) := by
            rw [hN_eq]
            ring
      _ ≤ (N : ℝ) * (∫ t in (-(T / 2))..(T / 2), f t) :=
        mul_le_mul_of_nonneg_left hcenterLower hNnonneg
      _ = ∫ t in (0 : ℝ)..1, f t := by rw [hunit, hcenter]
  have hunitNonneg : 0 ≤ (∫ t in (0 : ℝ)..1, f t) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    exact hnonneg t
  exact ⟨hunitNonneg, hunitUpper, hunitLower⟩

/-- Quantitative error of the zeroth memory average from its full relaxation
integral. The two losses are the fraction of the large period outside the
cutoff plateau and the residual exponential memory before that plateau. -/
theorem LMN_zero_unit_average_error {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) :
    |(∫ t in (0 : ℝ)..1, I.LMN κ m 0 t) -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹| ≤
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
        (5 * tauP β I.Λ m / tauPP β I.Λ m +
          Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
            tauP β I.Λ m)) := by
  let T := tauPP β I.Λ m
  let P := tauP β I.Λ m
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let L := ∫ t in (0 : ℝ)..1, I.LMN κ m 0 t
  have hT : 0 < T := by dsimp [T]; exact I.tauPP_pos' m
  have hP : 0 < P := by
    dsimp [P]
    exact Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    positivity
  have hL := LMN_zero_unit_average_bounds I hm κ hκ
  have hLlo : (1 / T * (T - 5 * P)) *
      ((1 - Real.exp (-ρ * P)) / ρ) ≤ L := by
    simpa [T, P, ρ, L] using hL.2.2
  have hLhi : L ≤ ρ⁻¹ := by
    simpa [T, P, ρ, L] using hL.2.1
  have hiden : ρ⁻¹ -
      ((1 / T * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ)) =
        ρ⁻¹ * (5 * P / T + Real.exp (-ρ * P) -
          (5 * P / T) * Real.exp (-ρ * P)) := by
    dsimp [ρ]
    field_simp [ne_of_gt hT, ne_of_gt hκ,
      ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)]
    ring
  have hsub : 0 ≤ (5 * P / T) * Real.exp (-ρ * P) := by positivity
  have hbound : ρ⁻¹ - L ≤ ρ⁻¹ *
      (5 * P / T + Real.exp (-ρ * P)) := by
    calc
      ρ⁻¹ - L ≤ ρ⁻¹ -
          ((1 / T * (T - 5 * P)) * ((1 - Real.exp (-ρ * P)) / ρ)) :=
        sub_le_sub_left hLlo _
      _ = ρ⁻¹ * (5 * P / T + Real.exp (-ρ * P) -
            (5 * P / T) * Real.exp (-ρ * P)) := hiden
      _ ≤ ρ⁻¹ * (5 * P / T + Real.exp (-ρ * P)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hρ.le)
        linarith [hsub]
  have habs : |L - ρ⁻¹| = ρ⁻¹ - L := by
    rw [abs_of_nonpos]
    · ring
    · linarith [hLhi]
  rw [habs]
  change ρ⁻¹ - L ≤ ρ⁻¹ * (5 * P / T + Real.exp (-ρ * P))
  exact hbound

theorem timeAvgMat_Kmat_entry_formula {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (i j : Fin 2) :
    timeAvgMat (I.Kmat κ m) i j =
      κ * (if i = j then 1 else 0) +
        ∑ n ∈ Finset.range (Nstar β),
          (∫ t in (0 : ℝ)..1, I.LMN κ m n t) *
            timeAvgMat (I.jMN κ m n) i j := by
  have hLMN (n : ℕ) : Continuous (I.LMN κ m n) :=
    (LMN_contDiff I hm hκ n).continuous
  have hJ (n : ℕ) : Continuous (fun t => I.jMN κ m n t i j) := by
    exact ((continuous_apply j).comp ((continuous_apply i).comp
      (jMN_continuous I m n κ)))
  have hterm (n : ℕ) : IntervalIntegrable
      (fun t => I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j) volume 0 1 :=
    ((hLMN n).mul continuous_const).intervalIntegrable 0 1
  have hsumInt : (∫ t in (0 : ℝ)..1,
      ∑ n ∈ Finset.range (Nstar β),
        I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j) =
      ∑ n ∈ Finset.range (Nstar β),
        ∫ t in (0 : ℝ)..1,
          I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j := by
    exact intervalIntegral.integral_finsetSum (fun n hn => hterm n)
  change (∫ t in (0 : ℝ)..1, I.Kmat κ m t i j) = _
  unfold Ingredients.Kmat
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.sum_apply]
  rw [intervalIntegral.integral_add]
  · rw [hsumInt]
    have hconst : (∫ t in (0 : ℝ)..1, κ * (if i = j then 1 else 0)) =
        κ * (if i = j then 1 else 0) := by
      simp [intervalIntegral.integral_const]
    rw [hconst]
    apply congrArg (fun x : ℝ => κ * (if i = j then 1 else 0) + x)
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_mul_const]
  · exact (continuous_const).intervalIntegrable 0 1
  · exact (continuous_finsetSum _ (fun n hn => (hLMN n).mul continuous_const)).intervalIntegrable
      0 1

/-- Integrating the explicit `L_mn` envelope preserves its pointwise bound.
This is the scalar ingredient used in the nonzero-order tail of the one-step
averaging estimate. -/
theorem LMN_unit_average_abs_le {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    |∫ t in (0 : ℝ)..1, I.LMN κ m n t| ≤
      (n.factorial : ℝ) * 2 ^ n *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t => I.LMN κ m n t)
    (fun t _ => by
      simpa only [Real.norm_eq_abs] using LMN_abs_le I hm hκ n t)
  simpa [Real.norm_eq_abs] using h

theorem OneStepAveraging.LMN_jMN_unit_average_product_le {β : ℝ}
    (I : Ingredients β) {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n)
    (hN : n ≤ Nstar β) {κ : ℝ} (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    |(∫ t in (0 : ℝ)..1, I.LMN κ m n t) *
        timeAvgMat (I.jMN κ m n) 0 0| ≤
      (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (2 * epsilon β I.Λ m ^ 2 /
          (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  let Q := 2 * epsilon β I.Λ m ^ 2 /
    (4 * Real.pi ^ 2 * κ * tau β I.Λ m)
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ1 : Q ≤ 1 := by
    dsimp [Q]
    apply (div_le_iff₀ (by positivity)).2
    have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hnum : 2 * epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m := by
      nlinarith [hcondition]
    calc
      2 * epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m := hnum
      _ ≤ (4 * Real.pi ^ 2) * (κ * tau β I.Λ m) :=
        by simpa using mul_le_mul_of_nonneg_right hπ (mul_nonneg hκ.le hτ.le)
      _ = 1 * (4 * Real.pi ^ 2 * κ * tau β I.Λ m) := by ring
  have hQpow : Q ^ n ≤ Q := by
    rw [← Nat.sub_add_cancel hn, pow_succ]
    calc
      Q ^ (n - 1) * Q ≤ 1 * Q :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hQ0 hQ1) hQ0
      _ = Q := by ring
  have hL := LMN_unit_average_abs_le I hm hκ n
  have hJ := jMN_average_entry_abs_le I m hN hκ 0 0
  have hmain :
      ((n.factorial : ℝ) * 2 ^ n *
          (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹) *
        ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
            (n.factorial : ℝ) *
          (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
          (I.Czeta / tau β I.Λ m ^ n)) =
      (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) * Q ^ n := by
    dsimp [Q]
    have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
    have hκne : κ ≠ 0 := ne_of_gt hκ
    have hτne : tau β I.Λ m ≠ 0 := ne_of_gt hτ
    have hεne : epsilon β I.Λ m ≠ 0 := ne_of_gt hε
    simp only [div_pow, mul_pow, inv_div]
    field_simp
    ring
  have hCz : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hD : 0 ≤ I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ := by
    positivity
  rw [abs_mul]
  calc
    |∫ t in (0 : ℝ)..1, I.LMN κ m n t| *
        |timeAvgMat (I.jMN κ m n) 0 0| ≤
      ((n.factorial : ℝ) * 2 ^ n *
          (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹) *
        ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
            (n.factorial : ℝ) *
          (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
          (I.Czeta / tau β I.Λ m ^ n)) :=
      mul_le_mul hL hJ (abs_nonneg _) (by positivity)
    _ = (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) * Q ^ n := hmain
    _ ≤ (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) * Q :=
      mul_le_mul_of_nonneg_left hQpow hD

/-- One-step estimate for the average of the `Kmat`.  The zeroth mode
produces the `9/80` increment; all positive orders form a geometric tail under
the source small-ratio condition. -/
theorem Kmat_average_one_step_error {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    |timeAvgMat (I.Kmat κ m) 0 0 -
        (κ + (9 / 80) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ))| ≤
      (9 / 80) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (5 * tauP β I.Λ m / tauPP β I.Λ m +
            Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
              tauP β I.Λ m)) +
        (Nstar β : ℝ) *
          (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
            (2 * epsilon β I.Λ m ^ 2 /
              (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) := by
  classical
  let R := Finset.range (Nstar β)
  let f := fun n : ℕ =>
    (∫ t in (0 : ℝ)..1, I.LMN κ m n t) *
      timeAvgMat (I.jMN κ m n) 0 0
  let L0 := ∫ t in (0 : ℝ)..1, I.LMN κ m 0 t
  let c0 := (9 * Real.pi ^ 2 / 20) *
    a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let loss := 5 * tauP β I.Λ m / tauPP β I.Λ m +
    Real.exp (-ρ * tauP β I.Λ m)
  let scale := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  let qrate := 2 * epsilon β I.Λ m ^ 2 /
    (4 * Real.pi ^ 2 * κ * tau β I.Λ m)
  have hNreq := Infra.Ingredients.Nstar_ge_requirement I.one_lt_beta I.beta_lt
  have hqparam := Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt
  have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
  have hδ := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hqminus : 0 < q β - 1 := by linarith [hqparam]
  have hbg : 0 < β + gamma β := by linarith [I.one_lt_beta, hγ]
  have hterm : 0 ≤ 4 * (q β - 1) * (β + gamma β) / delta β := by
    apply div_nonneg
    · positivity
    · exact hδ.le
  have hN8 : (8 : ℝ) ≤ (Nstar β : ℝ) := by linarith
  have hNnat : 8 ≤ Nstar β := by exact_mod_cast hN8
  have h0mem : 0 ∈ R := by
    dsimp [R]
    exact Finset.mem_range.mpr (by omega)
  have hsplit : (∑ n ∈ R, f n) = f 0 + ∑ n ∈ R.erase 0, f n := by
    rw [← Finset.sum_erase_add R f h0mem]
    ring
  have hJ0 : timeAvgMat (I.jMN κ m 0) 0 0 = c0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0)
      (jMN_zero_average_eq I hm κ)
    simpa [c0, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] using h
  have hlead : c0 * ρ⁻¹ = (9 / 80) * scale := by
    dsimp [c0, ρ, scale]
    have hκ : κ ≠ 0 := ne_of_gt hκ
    have hε : epsilon β I.Λ m ≠ 0 := ne_of_gt
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
    field_simp
    ring
  have hc0 : 0 ≤ c0 := by positivity
  have hLerr := LMN_zero_unit_average_error I hm κ hκ
  have hmainErr : |L0 * c0 - (9 / 80) * scale| ≤
      (9 / 80) * scale * loss := by
    have hdiff : L0 * c0 - (9 / 80) * scale = c0 * (L0 - ρ⁻¹) := by
      rw [← hlead]
      ring
    have hLerr' : |L0 - ρ⁻¹| ≤ ρ⁻¹ * loss := by
      simpa [L0, ρ, loss] using hLerr
    rw [hdiff, abs_mul, abs_of_nonneg hc0]
    calc
      c0 * |L0 - ρ⁻¹| ≤ c0 * (ρ⁻¹ * loss) :=
        mul_le_mul_of_nonneg_left hLerr' hc0
      _ = (9 / 80) * scale * loss := by
        calc
          c0 * (ρ⁻¹ * loss) = (c0 * ρ⁻¹) * loss := by ring
          _ = (9 / 80) * scale * loss := by rw [hlead]
  have hτm : 0 < tau β I.Λ m := I.tau_pos' m
  have hεm : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hQ0 : 0 ≤ qrate := by
    dsimp [qrate]
    exact div_nonneg (by positivity) (by positivity)
  have hD : 0 ≤ I.Czeta * scale := by
    dsimp [scale]
    have hCz : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
    positivity
  have hrestTerm : ∀ n ∈ R.erase 0,
      |f n| ≤ (I.Czeta * scale) * qrate := by
    intro n hn
    have hnmem : n ∈ R := (Finset.mem_erase.mp hn).2
    have hnpos : 0 < n := Nat.pos_of_ne_zero (Finset.mem_erase.mp hn).1
    have hnN : n ≤ Nstar β := by
      dsimp [R] at hnmem
      exact Nat.le_of_lt (Finset.mem_range.mp hnmem)
    have hprod := OneStepAveraging.LMN_jMN_unit_average_product_le I hm hnpos hnN hκ hcondition
    change |(∫ t in (0 : ℝ)..1, I.LMN κ m n t) *
      timeAvgMat (I.jMN κ m n) 0 0| ≤ _ at hprod
    calc
      |(∫ t in (0 : ℝ)..1, I.LMN κ m n t) *
          timeAvgMat (I.jMN κ m n) 0 0| ≤
        (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) * qrate := by
          simpa [qrate] using hprod
      _ = (I.Czeta * scale) * qrate := by dsimp [scale]; ring
  have hrest : |∑ n ∈ R.erase 0, f n| ≤
      (Nstar β : ℝ) * (I.Czeta * scale) * qrate := by
    have hsum := Finset.abs_sum_le_sum_abs f (R.erase 0)
    have hmajor := Finset.sum_le_sum (fun n hn => hrestTerm n hn)
    have hcard : ((R.erase 0).card : ℝ) ≤ (Nstar β : ℝ) := by
      have hnat : (R.erase 0).card ≤ (R.card) :=
        Finset.card_le_card (Finset.erase_subset (0 : ℕ) R)
      rw [show R.card = Nstar β by simp [R]] at hnat
      exact_mod_cast hnat
    have hsumconst : (∑ _n ∈ R.erase 0, (I.Czeta * scale) * qrate) =
        ((R.erase 0).card : ℝ) * ((I.Czeta * scale) * qrate) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc
      |∑ n ∈ R.erase 0, f n| ≤ ∑ n ∈ R.erase 0, |f n| := hsum
      _ ≤ ∑ _n ∈ R.erase 0, (I.Czeta * scale) * qrate := hmajor
      _ ≤ (Nstar β : ℝ) * (I.Czeta * scale) * qrate := by
        rw [hsumconst]
        calc
          ((R.erase 0).card : ℝ) * ((I.Czeta * scale) * qrate) ≤
              (Nstar β : ℝ) * ((I.Czeta * scale) * qrate) :=
            mul_le_mul_of_nonneg_right hcard (mul_nonneg hD hQ0)
          _ = (Nstar β : ℝ) * (I.Czeta * scale) * qrate := by ring
  have hentry := timeAvgMat_Kmat_entry_formula I hm κ hκ 0 0
  have hformula : timeAvgMat (I.Kmat κ m) 0 0 = κ + f 0 +
      ∑ n ∈ R.erase 0, f n := by
    rw [hentry]
    simp only [Fin.isValue, ↓reduceIte, mul_one]
    rw [hsplit]
    dsimp [f]
    rw [hJ0]
    ring
  have heq : timeAvgMat (I.Kmat κ m) 0 0 -
      (κ + (9 / 80) * scale) =
        (L0 * c0 - (9 / 80) * scale) + ∑ n ∈ R.erase 0, f n := by
    rw [hformula]
    dsimp [f]
    rw [hJ0]
    dsimp [L0, c0]
    ring
  rw [heq]
  calc
    |(L0 * c0 - (9 / 80) * scale) + ∑ n ∈ R.erase 0, f n| ≤
        |L0 * c0 - (9 / 80) * scale| + |∑ n ∈ R.erase 0, f n| := abs_add_le _ _
    _ ≤ (9 / 80) * scale * loss +
        (Nstar β : ℝ) * (I.Czeta * scale) * qrate := add_le_add hmainErr hrest
    _ = (9 / 80) * scale *
          (5 * tauP β I.Λ m / tauPP β I.Λ m +
            Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
              tauP β I.Λ m)) +
        (Nstar β : ℝ) *
          (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (2 * epsilon β I.Λ m ^ 2 /
              (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) := by
      dsimp [scale, loss, qrate, ρ]
      ring

/-- One-step estimate for the actual averaged flux `KhomScalar`, retaining
both justified finite-regularity errors from `Approx.lean`. The extra
`(tau/tauP)^Nstar` term is not silently replaced by the `q^Nstar` term. -/
theorem KhomScalar_one_step_error_finite {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    |I.KhomScalar κ m -
        (κ + (9 / 80) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ))| ≤
      (9 / 80) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (5 * tauP β I.Λ m / tauPP β I.Λ m +
            Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
              tauP β I.Λ m)) +
        (Nstar β : ℝ) *
          (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
            (2 * epsilon β I.Λ m ^ 2 /
              (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) +
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
              (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β +
            (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
              2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
              (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) := by
  have happrox := Kmat_average_sub_Khom_norm_le_finite I hm hκ hcondition
  have hentry : |timeAvgMat (I.Kmat κ m) 0 0 - I.KhomScalar κ m| ≤
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β +
          (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
            2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
            (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) := by
    have hpi := (norm_le_pi_norm
        ((timeAvgMat (I.Kmat κ m) - I.Khom κ m) 0) 0).trans
      ((norm_le_pi_norm (timeAvgMat (I.Kmat κ m) - I.Khom κ m) 0).trans happrox)
    have hscalar : I.KhomScalar κ m = I.Khom κ m 0 0 := rfl
    simpa [Real.norm_eq_abs, Matrix.sub_apply, hscalar] using hpi
  have hsym : |I.KhomScalar κ m - timeAvgMat (I.Kmat κ m) 0 0| ≤
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β +
          (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
            2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
            (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) := by
    simpa [abs_sub_comm] using hentry
  have hKmat := Kmat_average_one_step_error I hm hκ hcondition
  have htri := abs_sub_le (I.KhomScalar κ m)
    (timeAvgMat (I.Kmat κ m) 0 0)
    (κ + (9 / 80) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ))
  calc
    _ ≤ |I.KhomScalar κ m - timeAvgMat (I.Kmat κ m) 0 0| +
        |timeAvgMat (I.Kmat κ m) 0 0 -
          (κ + (9 / 80) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ))| := htri
    _ ≤ (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
              (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β +
            (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
              2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
              (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) +
        |timeAvgMat (I.Kmat κ m) 0 0 -
          (κ + (9 / 80) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ))| :=
            add_le_add hsym (le_refl _)
    _ ≤ _ := add_le_add (le_refl _) hKmat
    _ = _ := by ring

/-- Ingredient-uniform form of the one-step estimate under the cutoff bounds
used by the diffusivity-recursion estimate. Its constants depend on `β` and `C₀`, not on the
    chosen `I`. -/
theorem KhomScalar_one_step_error_finite_uniform {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    |I.KhomScalar κ m -
        (κ + (9 / 80) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ))| ≤
      (9 / 80) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (5 * tauP β I.Λ m / tauPP β I.Λ m +
            Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
              tauP β I.Λ m)) +
        (Nstar β : ℝ) *
          (C₀ * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
            (2 * epsilon β I.Λ m ^ 2 /
              (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) +
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          ((4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β) *
              (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β +
            (2 * Nstar β * C₀ * ((Nstar β).factorial : ℝ) *
              2 ^ Nstar β * 2 ^ Nstar β * C₀ ^ 2 * 8 ^ Nstar β) *
              (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) := by
  have hbase := KhomScalar_one_step_error_finite I hm hκ hcondition
  have hCz0 : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hCh0 : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hC00 : 0 ≤ C₀ := le_trans hCz0 hCz
  have hChatSq : I.Chat ^ 2 ≤ C₀ ^ 2 :=
    (sq_le_sq₀ hCh0 hC00).2 hCh
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hτP : 0 < tauP β I.Λ m :=
    Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hscale : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ := by positivity
  have hq : 0 ≤ epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) := by positivity
  have hs : 0 ≤ tau β I.Λ m / tauP β I.Λ m := by positivity
  calc
    _ ≤ (9 / 80) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (5 * tauP β I.Λ m / tauPP β I.Λ m +
            Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
              tauP β I.Λ m)) +
        (Nstar β : ℝ) *
          (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
            (2 * epsilon β I.Λ m ^ 2 /
              (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) +
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
              (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β +
            (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
              2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
              (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) := hbase
    _ ≤ _ := by
      gcongr

end AVenhance.Infra.Section3

end
