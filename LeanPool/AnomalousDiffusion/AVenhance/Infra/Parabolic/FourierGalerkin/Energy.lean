/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Energy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Existence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Gronwall
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ODE
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Energy estimate for a finite Galerkin system

The finite weak-form matrix splits into transport and diffusion forms. The transport contribution
is bounded by `B ‖D u‖ ‖u‖`; Young's inequality absorbs one diffusion term and leaves a scalar
Grönwall coefficient `B² / κ`. The result below takes those two finite-dimensional form facts as
its interface, so the spatial mode calculus can establish them independently.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Young's inequality in the form used to absorb the drift into diffusion. -/
theorem drift_absorption {κ B g u q : ℝ} (hκ : 0 < κ)
    (hq : |q| ≤ B * g * u) :
    -2 * q - 2 * κ * g ^ 2 ≤ (B ^ 2 / κ) * u ^ 2 - κ * g ^ 2 := by
  have hq' : -q ≤ B * g * u := by
    calc
      -q ≤ |q| := neg_le_abs q
      _ ≤ B * g * u := hq
  have hsq : 0 ≤ (κ * g - B * u) ^ 2 := sq_nonneg (κ * g - B * u)
  have hyoung : 2 * B * g * u ≤ κ * g ^ 2 + (B ^ 2 / κ) * u ^ 2 := by
    have hκne : κ ≠ 0 := ne_of_gt hκ
    field_simp [hκne]
    nlinarith [hsq]
  nlinarith

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Grönwall control of a homogeneous finite-dimensional ODE with a dissipative weak form.

`gradient` is the finite-mode spatial gradient map and `driftForm` is the tested
`∫ (b · D u) u` term. `hform` is the coefficient-space identity obtained by testing the projected
weak equation against the current Galerkin state. `hdrift` is the Cauchy-Schwarz estimate using
the essential bound on `b`; no divergence-free condition is used. -/
theorem galerkin_energy_estimate
    {D : AVenhance.Infra.ODE.LinearODEData (E := E) 0 1 (by norm_num)}
    (u : C(Icc (0 : ℝ) 1, E)) (hu : D.IsSolution u)
    (hforcing : D.f = 0)
    (gradient : E →L[ℝ] F) (κ B : ℝ) (hκ : 0 < κ)
    (driftForm : ℝ → E → ℝ)
    (hform : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ v,
      2 * inner ℝ v (D.A t v) =
        -2 * driftForm t v - 2 * κ * ‖gradient v‖ ^ 2)
    (hdrift : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ v,
      |driftForm t v| ≤ B * ‖gradient v‖ * ‖v‖) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 ≤
        ‖D.y₀‖ ^ 2 * Real.exp (B ^ 2 / κ * t) ∧
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 +
          κ * ∫ s in 0..t,
            ‖gradient (AVenhance.Infra.ODE.extendCurve (by norm_num) u s)‖ ^ 2 ≤
        ‖D.y₀‖ ^ 2 +
          (B ^ 2 / κ) *
            (t * ‖D.y₀‖ ^ 2 * Real.exp (B ^ 2 / κ * t)) := by
  let y : ℝ → E := AVenhance.Infra.ODE.extendCurve (by norm_num) u
  let z : ℝ → ℝ := fun s => ‖y s‖ ^ 2
  let g : ℝ → ℝ := fun s => ‖gradient (y s)‖ ^ 2
  let c : ℝ := B ^ 2 / κ
  have hc : 0 ≤ c := div_nonneg (sq_nonneg B) hκ.le
  have hycont : Continuous y := AVenhance.Infra.ODE.continuous_extendCurve (by norm_num) u
  have hzcont : Continuous z := by
    exact (continuous_norm.comp hycont).pow 2
  have hgcont : Continuous g := by
    exact (continuous_norm.comp (gradient.continuous.comp hycont)).pow 2
  have hzInt : IntervalIntegrable z volume 0 1 :=
    hzcont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hgInt : IntervalIntegrable g volume 0 1 :=
    hgcont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hczInt : IntervalIntegrable (fun s => c * z s) volume 0 1 := hzInt.const_mul c
  let q : ℝ → ℝ := fun s => 2 * inner ℝ (y s) (D.A s (y s))
  have hAC : AbsolutelyContinuousOnInterval z 0 1 := by
    simpa [z, y] using hu.energy_absolutelyContinuous D
  have hqDeriv := hu.ae_energy_deriv D
  have hq_eq_deriv : q =ᵐ[volume.restrict (uIoc 0 1)] deriv z := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [hqDeriv] with s hs hsmem
    have hsmem' : s ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (uIoc_subset_uIcc hsmem)
    have hderiv := hs hsmem'
    have hfs : D.f s = 0 := congrFun hforcing s
    simpa [q, z, y, hfs] using hderiv.deriv.symm
  have hqInt : IntervalIntegrable q volume 0 1 :=
    hAC.intervalIntegrable_deriv |>.congr_ae hq_eq_deriv.symm
  have hpoint_y : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      q s ≤ c * z s - κ * g s := by
    filter_upwards [hform, hdrift] with s hform_s hdrift_s
    have hyoung := drift_absorption hκ (hdrift_s (y s))
    have hpoint : 2 * inner ℝ (y s) (D.A s (y s)) ≤
        c * ‖y s‖ ^ 2 - κ * ‖gradient (y s)‖ ^ 2 := by
      rw [hform_s (y s)]
      dsimp [c]
      nlinarith [hyoung]
    simpa [q, z, g, y] using hpoint
  have hzero : y 0 = D.y₀ := by
    have hsol := hu.integralSolution D
    have h := hsol 0 ⟨le_rfl, by norm_num⟩
    simpa [y, AVenhance.Infra.ODE.linearRhs, hforcing] using h
  have hidentity (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∫ s in 0..t, q s = z t - z 0 := by
    have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hsol := hu.integralSolution D
    have hsolT : AVenhance.Infra.ODE.IsLinearIntegralSolution D.A D.f D.y₀ 0 t y := by
      intro s hs
      exact hsol s ⟨hs.1, hs.2.trans ht.2⟩
    have hrhsT : IntervalIntegrable
        (AVenhance.Infra.ODE.linearRhs D.A D.f y) volume 0 t := by
      change IntervalIntegrable (D.rhs u) volume 0 t
      exact (D.rhs_intervalIntegrable u).mono_set hsubset
    have hid := AVenhance.Infra.ODE.IsLinearIntegralSolution.energy_identity ht.1 hsolT hrhsT
    simpa [q, z, y, AVenhance.Infra.ODE.linearRhs, hforcing] using hid
  have hineq : ∀ t ∈ Icc (0 : ℝ) 1,
      z t ≤ z 0 + ∫ s in 0..t, c * z s := by
    intro t ht
    have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hqT := hqInt.mono_set hsubset
    have hczT := hczInt.mono_set hsubset
    have hpointT : q ≤ᵐ[volume.restrict (Icc 0 t)] fun s => c * z s := by
      have hsubsetIcc : Icc (0 : ℝ) t ⊆ Icc 0 1 := by
        intro s hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      have hsmall := ae_mono (Measure.restrict_mono hsubsetIcc le_rfl) hpoint_y
      filter_upwards [hsmall] with s hs
      have hg0 : 0 ≤ g s := sq_nonneg ‖gradient (y s)‖
      have hκg : 0 ≤ κ * g s := mul_nonneg hκ.le hg0
      calc
        q s ≤ c * z s - κ * g s := hs
        _ ≤ c * z s := by nlinarith [hκg]
    have hint := intervalIntegral.integral_mono_ae_restrict ht.1 hqT hczT hpointT
    rw [hidentity t ht] at hint
    dsimp [c] at ⊢ hint
    linarith
  have hconstC : IntervalIntegrable (fun _ : ℝ => c) volume 0 1 := intervalIntegrable_const
  have hgronwall := AVenhance.Infra.ODE.integral_gronwall_bound
    (a := 0) (b := 1) (C := z 0) (show (0 : ℝ) ≤ 1 by norm_num)
    hconstC hczInt (fun _ _ => hc) hineq
  intro t ht
  have hnorm := hgronwall t ht
  have hexp : ∫ s in 0..t, c = c * t := by
    simp [intervalIntegral.integral_const]
    ring
  have hnorm' : z t ≤ z 0 * Real.exp (c * t) := by
    rw [hexp] at hnorm
    exact hnorm
  have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hqT := hqInt.mono_set hsubset
  have hrhsInt : IntervalIntegrable (fun s => c * z s - κ * g s) volume 0 1 :=
    hczInt.sub (hgInt.const_mul κ)
  have hrhsT := hrhsInt.mono_set hsubset
  have hpointT : q ≤ᵐ[volume.restrict (Icc 0 t)]
      fun s => c * z s - κ * g s := by
    have hsubsetIcc : Icc (0 : ℝ) t ⊆ Icc 0 1 := by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    exact ae_mono (Measure.restrict_mono hsubsetIcc le_rfl) hpoint_y
  have hint := intervalIntegral.integral_mono_ae_restrict ht.1 hqT hrhsT hpointT
  rw [hidentity t ht] at hint
  have henergy : z t + κ * ∫ s in 0..t, g s ≤ z 0 + c * ∫ s in 0..t, z s := by
    dsimp [c] at hint ⊢
    rw [intervalIntegral.integral_sub (hczInt.mono_set hsubset)
      ((hgInt.const_mul κ).mono_set hsubset)] at hint
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
    dsimp [g] at hint
    nlinarith
  have hz0 : 0 ≤ z 0 := sq_nonneg ‖y 0‖
  have hpointBound : ∀ s ∈ Icc 0 t, z s ≤ z 0 * Real.exp (c * t) := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hbs := hgronwall s hsIcc
    have hcs : c * s ≤ c * t := mul_le_mul_of_nonneg_left hs.2 hc
    calc
      z s ≤ z 0 * Real.exp (c * s) := by
        have hexps' : ∫ r in 0..s, c = c * s := by
          simp [intervalIntegral.integral_const]
          ring
        rw [hexps'] at hbs
        exact hbs
      _ ≤ z 0 * Real.exp (c * t) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcs) hz0
  have hconstInt : IntervalIntegrable (fun _ : ℝ => z 0 * Real.exp (c * t)) volume 0 t :=
    intervalIntegrable_const
  have hintZ := intervalIntegral.integral_mono_on ht.1 (hzInt.mono_set hsubset)
    hconstInt hpointBound
  have hintZ' : ∫ s in 0..t, z s ≤ t * z 0 * Real.exp (c * t) := by
    calc
      ∫ s in 0..t, z s ≤ ∫ s in 0..t, z 0 * Real.exp (c * t) := hintZ
      _ = t * z 0 * Real.exp (c * t) := by
        simp [intervalIntegral.integral_const]
        ring
  have henergy' : z t + κ * ∫ s in 0..t, g s ≤
      z 0 + c * (t * z 0 * Real.exp (c * t)) := by
    have hmul := mul_le_mul_of_nonneg_left hintZ' hc
    calc
      z t + κ * ∫ s in 0..t, g s ≤ z 0 + c * ∫ s in 0..t, z s := henergy
      _ ≤ z 0 + c * (t * z 0 * Real.exp (c * t)) := by
        linarith
  have hz0_eq : z 0 = ‖D.y₀‖ ^ 2 := by
    dsimp [z]
    rw [hzero]
  constructor
  · simpa [z, y, c, hz0_eq] using hnorm'
  · simpa [g, z, y, c, hz0_eq] using henergy'

/-- The energy estimate specialized to a finite real weak-form Galerkin system. -/
theorem WeakFormGalerkinData.IsSolution.energyEstimate
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : WeakFormGalerkinData n F)
    (u : C(Icc (0 : ℝ) 1, Coefficients n)) (hu : D.ode.IsSolution u) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 ≤
        ‖D.initial‖ ^ 2 * Real.exp (D.driftBound ^ 2 / D.diffusivity * t) ∧
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 +
          D.diffusivity * ∫ s in 0..t,
            ‖D.gradient (AVenhance.Infra.ODE.extendCurve (by norm_num) u s)‖ ^ 2 ≤
        ‖D.initial‖ ^ 2 +
          (D.driftBound ^ 2 / D.diffusivity) *
            (t * ‖D.initial‖ ^ 2 *
              Real.exp (D.driftBound ^ 2 / D.diffusivity * t)) := by
  simpa [WeakFormGalerkinData.ode] using
    galerkin_energy_estimate (D := D.ode) u hu rfl D.gradient D.diffusivity
      D.driftBound D.diffusivity_pos D.driftForm D.weakForm_energy D.drift_bound

/-- Uniqueness of the absolutely-continuous coefficient path for fixed Galerkin data. -/
theorem WeakFormGalerkinData.IsSolution.unique
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : WeakFormGalerkinData n F)
    {u v : C(Icc (0 : ℝ) 1, Coefficients n)}
    (hu : D.ode.IsSolution u) (hv : D.ode.IsSolution v) : u = v := by
  obtain ⟨w, hw⟩ := D.existsUnique_solution
  rcases hw with ⟨_, hw_unique⟩
  have hwu : u = w := hw_unique u ⟨hu.integralSolution D.ode,
    hu.absolutelyContinuousOnInterval D.ode⟩
  have hwv : v = w := hw_unique v ⟨hv.integralSolution D.ode,
    hv.absolutelyContinuousOnInterval D.ode⟩
  exact hwu.trans hwv.symm

end AVenhance.Infra.Parabolic.FourierGalerkin

end
