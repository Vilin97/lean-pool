/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Existence
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Variable-coefficient Grönwall estimate

The scalar comparison argument below allows an integrable, time-dependent coefficient.  This is
the form needed when the linear operator is merely measurable: replacing its integral by a uniform
bound would lose information.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace AVenhance.Infra.ODE

theorem Gronwall.integral_gronwall_endpoint {a b C : ℝ} (hab : a ≤ b)
    {c z : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b)
    (hcz : IntervalIntegrable (fun t => c t * z t) volume a b)
    (hc_nonneg : ∀ t ∈ Icc a b, 0 ≤ c t)
    (hineq : ∀ t ∈ Icc a b,
      z t ≤ C + ∫ s in a..t, c s * z s) :
    z b ≤ C * Real.exp (∫ t in a..b, c t) := by
  let A := fun t : ℝ => ∫ s in a..t, c s
  let V := fun t : ℝ => C + ∫ s in a..t, c s * z s
  let W := fun t : ℝ => Real.exp (-A t)
  let P := fun t : ℝ => V t * W t
  have hAac : AbsolutelyContinuousOnInterval A a b := by
    simpa [A] using hc.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hVac : AbsolutelyContinuousOnInterval V a b := by
    have hprim := hcz.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) a b := by
      rw [absolutelyContinuousOnInterval_iff]
      intro ε hε
      exact ⟨ε, hε, by intro J hJ hlen; simpa using hε⟩
    exact (hconst.add hprim).congr (by intro t ht; rfl)
  have hAbound := hAac.exists_bound
  obtain ⟨B, hB⟩ := hAbound
  let B₀ := max B 0
  have hAabs (t : ℝ) (ht : t ∈ uIcc a b) : |A t| ≤ B₀ := by
    have h := hB t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hWac : AbsolutelyContinuousOnInterval W a b := by
    have hexp : ContDiffOn ℝ 1 Real.exp (Icc (-B₀) B₀) := by
      simpa using Real.contDiff_exp.contDiffOn
    obtain ⟨K, hK⟩ := hexp.exists_lipschitzOnWith (by norm_num)
      (convex_Icc _ _) isCompact_Icc
    have hmap : MapsTo (fun t => -A t) (uIcc a b) (Icc (-B₀) B₀) := by
      intro t ht
      rw [mem_Icc]
      have habs := hAabs t ht
      rw [abs_le] at habs
      constructor <;> linarith
    simpa [W, A, Function.comp_def] using
      hK.comp_absolutelyContinuousOnInterval hmap hAac.neg
  have hPac : AbsolutelyContinuousOnInterval P a b := by
    change AbsolutelyContinuousOnInterval (V * W) a b
    exact hVac.mul hWac
  have hVderiv : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt V (c t * z t) t := by
    filter_upwards [hcz.ae_hasDerivAt_integral] with t ht
    intro htmem
    have h := ht htmem a (by simp)
    (convert (hasDerivAt_const t C).add h using 1; simp)
  have hAderiv : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt A (c t) t := by
    filter_upwards [hc.ae_hasDerivAt_integral] with t ht
    intro htmem
    exact ht htmem a (by simp)
  have hWderiv : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt W (-(W t * c t)) t := by
    filter_upwards [hAderiv] with t ht
    intro htmem
    have hneg := (ht htmem).neg
    have h : HasDerivAt (fun s => Real.exp (-A s))
        (-(Real.exp (-A t) * c t)) t := by
      convert (Real.hasDerivAt_exp (-A t)).comp t hneg using 1
      · rfl
      · ring
    simpa [W] using h
  have hPderiv : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt P (c t * z t * W t + V t * (-(W t * c t))) t := by
    filter_upwards [hVderiv, hWderiv] with t hV hW
    intro htmem
    exact (hV htmem).mul (hW htmem)
  have hPderiv_nonpos :
      ∀ᵐ t ∂(volume.restrict (Icc a b)), deriv P t ≤ 0 := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hPderiv] with t ht htmem
    have hderiv := (ht (uIcc_of_le hab ▸ htmem)).deriv
    rw [hderiv]
    have hc0 := hc_nonneg t htmem
    have hW0 : 0 ≤ W t := le_of_lt (Real.exp_pos _)
    have hzV : z t - V t ≤ 0 := by
      dsimp [V]
      exact sub_nonpos.mpr (hineq t htmem)
    calc
      c t * z t * W t + V t * (-(W t * c t)) = c t * W t * (z t - V t) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc0 hW0) hzV
  have hPint := hPac.intervalIntegrable_deriv
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b := by simp
  have hPint_nonpos := intervalIntegral.integral_mono_ae_restrict hab hPint hzero
    hPderiv_nonpos
  have hFTC := hPac.integral_deriv_eq_sub
  have hPend : P b ≤ P a := by
    have hdiff : P b - P a ≤ 0 := by
      rw [← hFTC]
      simpa using hPint_nonpos
    exact sub_nonpos.mp hdiff
  have hPa : P a = C := by simp [P, V, W, A]
  have hPend' : V b * W b ≤ C := by simpa [P, hPa] using hPend
  have hmul := mul_le_mul_of_nonneg_right hPend' (le_of_lt (Real.exp_pos (A b)))
  have hVb : V b ≤ C * Real.exp (A b) := by
    have hExp : Real.exp (-A b) * Real.exp (A b) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have heq : V b = (V b * W b) * Real.exp (A b) := by
      calc
        V b = V b * (Real.exp (-A b) * Real.exp (A b)) := by rw [hExp, mul_one]
        _ = (V b * W b) * Real.exp (A b) := by simp [W]; ring
    calc
      V b = (V b * W b) * Real.exp (A b) := heq
      _ ≤ C * Real.exp (A b) := by simpa [mul_assoc] using hmul
  have hzbV : z b ≤ V b := by
    simpa [V] using hineq b ⟨hab, le_rfl⟩
  exact hzbV.trans hVb

/-- Integral Grönwall inequality with a nonnegative integrable time-dependent coefficient.
The additive constant may already include an integral of an inhomogeneous forcing term. -/
theorem integral_gronwall_bound {a b C : ℝ} (hab : a ≤ b) {c z : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b)
    (hcz : IntervalIntegrable (fun t => c t * z t) volume a b)
    (hc_nonneg : ∀ t ∈ Icc a b, 0 ≤ c t)
    (hineq : ∀ t ∈ Icc a b,
      z t ≤ C + ∫ s in a..t, c s * z s) :
    ∀ t ∈ Icc a b, z t ≤ C * Real.exp (∫ s in a..t, c s) := by
  intro t ht
  have hat : a ≤ t := ht.1
  have htb : t ≤ b := ht.2
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le hat, uIcc_of_le hab]
    intro s hs
    exact ⟨hs.1, hs.2.trans htb⟩
  have hc' : IntervalIntegrable c volume a t := hc.mono_set hsub
  have hcz' : IntervalIntegrable (fun s => c s * z s) volume a t := hcz.mono_set hsub
  have hnonneg' : ∀ s ∈ Icc a t, 0 ≤ c s := fun s hs => hc_nonneg s ⟨hs.1, hs.2.trans htb⟩
  have hineq' : ∀ s ∈ Icc a t, z s ≤ C + ∫ r in a..s, c r * z r :=
    fun s hs => hineq s ⟨hs.1, hs.2.trans htb⟩
  exact Gronwall.integral_gronwall_endpoint hat hc' hcz' hnonneg' hineq'

namespace LinearODEData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ} {hab : a ≤ b}

/-- The norm of the unique integral solution is controlled by the L¹ norms of the forcing and
operator coefficient. -/
theorem IsSolution.norm_le_gronwall
    (D : LinearODEData (E := E) a b hab) (u : C(Icc a b, E))
    (hu : D.IsSolution u) :
    ∀ t ∈ Icc a b,
      ‖extendCurve hab u t‖ ≤
        (‖D.y₀‖ + ∫ s in a..b, ‖D.f s‖) *
          Real.exp (∫ s in a..t, ‖D.A s‖) := by
  let y := extendCurve hab u
  let c := fun t : ℝ => ‖D.A t‖
  let z := fun t : ℝ => ‖y t‖
  let F := fun t : ℝ => ‖D.f t‖
  have hy := hu.integralSolution D
  have hAmeas0 : AEStronglyMeasurable c volume := by
    exact continuous_norm.comp_aestronglyMeasurable D.operator_aestronglyMeasurable
  have hAmeas : AEStronglyMeasurable c (volume.restrict (uIoc a b)) :=
    hAmeas0.mono_measure Measure.restrict_le_self
  have hAintOn : IntegrableOn c (uIoc a b) volume := by
    refine IntegrableOn.of_bound (s := uIoc a b) (μ := volume) ?_ hAmeas
      D.operatorBound ?_
    · rw [uIoc_of_le hab]
      exact measure_Ioc_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      simpa [c] using D.operator_norm_le t
  have hc : IntervalIntegrable c volume a b := by
    apply intervalIntegrable_iff.mpr
    simpa [c] using hAintOn
  have hcontY : Continuous y := continuous_extendCurve hab u
  have hzcont : Continuous z := by
    change Continuous (fun t => ‖y t‖)
    exact continuous_norm.comp hcontY
  have hcZ : IntervalIntegrable (fun t => c t * z t) volume a b :=
    hc.mul_continuousOn (by simpa [z] using hzcont.continuousOn)
  have hF : IntervalIntegrable F volume a b := by
    simpa [F] using D.forcing_intervalIntegrable.norm
  have hFnonneg : ∀ t ∈ Icc a b, 0 ≤ F t := by intro t ht; simp [F]
  have hineq : ∀ t ∈ Icc a b,
      z t ≤ (‖D.y₀‖ + ∫ s in a..b, F s) + ∫ s in a..t, c s * z s := by
    intro t ht
    have hat : a ≤ t := ht.1
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le hat, uIcc_of_le hab]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hsubtb : uIcc t b ⊆ uIcc a b := by
      rw [uIcc_of_le ht.2, uIcc_of_le hab]
      intro s hs
      exact ⟨le_trans hat hs.1, hs.2⟩
    have hRint : IntervalIntegrable (linearRhs D.A D.f y) volume a t := by
      have h := D.rhs_intervalIntegrable u
      exact h.mono_set hsub
    have hsumint : IntervalIntegrable (fun s => c s * z s + F s) volume a t :=
      (hcZ.mono_set hsub).add (hF.mono_set hsub)
    have hpt : ∀ s ∈ Icc a t,
        ‖linearRhs D.A D.f y s‖ ≤ c s * z s + F s := by
      intro s hs
      calc
        ‖linearRhs D.A D.f y s‖ ≤ ‖D.A s (y s)‖ + ‖D.f s‖ := norm_add_le _ _
        _ ≤ c s * z s + F s := by
          simpa [c, z, F] using add_le_add_right ((D.A s).le_opNorm (y s)) ‖D.f s‖
    have hnormint := intervalIntegral.norm_integral_le_integral_norm (a := a) (b := t)
      (μ := volume) hat (f := linearRhs D.A D.f y)
    have hmajor := intervalIntegral.integral_mono_on hat (hRint.norm) hsumint hpt
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hF.mono_set hsub) (hF.mono_set hsubtb)
    have htail : 0 ≤ ∫ s in t..b, F s :=
      intervalIntegral.integral_nonneg ht.2 (fun s hs => hFnonneg s ⟨le_trans ht.1 hs.1, hs.2⟩)
    have hforce : ∫ s in a..t, F s ≤ ∫ s in a..b, F s := by linarith
    have hadd := intervalIntegral.integral_add
      (hcZ.mono_set hsub) (hF.mono_set hsub)
    have hyt : y t = D.y₀ + ∫ s in a..t, linearRhs D.A D.f y s := hy t ht
    calc
      z t = ‖D.y₀ + ∫ s in a..t, linearRhs D.A D.f y s‖ := by rw [← hyt]
      _ ≤ ‖D.y₀‖ + ‖∫ s in a..t, linearRhs D.A D.f y s‖ := norm_add_le _ _
      _ ≤ ‖D.y₀‖ + ∫ s in a..t, ‖linearRhs D.A D.f y s‖ := by
        linarith [hnormint]
      _ ≤ ‖D.y₀‖ + ∫ s in a..t, c s * z s + F s :=
        by linarith [hmajor]
      _ = ‖D.y₀‖ + (∫ s in a..t, c s * z s) + ∫ s in a..t, F s := by
        rw [hadd]
        ring
      _ ≤ (‖D.y₀‖ + ∫ s in a..b, F s) + ∫ s in a..t, c s * z s := by
        linarith
  have hnonneg : ∀ t ∈ Icc a b, 0 ≤ c t := by intro t ht; simp [c]
  have hbound := integral_gronwall_bound hab hc hcZ hnonneg hineq
  intro t ht
  simpa [y, z, c, F] using hbound t ht

end LinearODEData

end AVenhance.Infra.ODE
