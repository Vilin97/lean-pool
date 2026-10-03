/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.CorrTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxStructure
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Continuity of the explicit single-mode memory integral. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open scoped ContDiff
open scoped Topology

namespace AVenhance.Infra.Section3

open AVenhance

theorem CorrTimeRegularity.zetaMK_hasCompactSupport {β : ℝ} (I : Ingredients β)
    {m : ℕ} (k : ℤ) : HasCompactSupport (I.zetaMK m k) := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  let e : ℝ ≃ₜ ℝ :=
    (Homeomorph.addRight (-((k : ℝ) * tau β I.Λ m))).trans
      (Homeomorph.mulRight₀ ((tau β I.Λ m)⁻¹)
        (inv_ne_zero (ne_of_gt hτ)))
  have he : I.zetaMK m k = I.zeta ∘ e := by
    funext t
    change I.zeta ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) =
      I.zeta (e t)
    congr 1
  rw [he]
  exact I.zeta_compact.comp_isClosedEmbedding e.isClosedEmbedding

theorem zetaProd_continuous {β : ℝ} (I : Ingredients β)
    {m : ℕ} (k : ℤ) : Continuous (I.zetaProd m k) := by
  have hhat : Continuous (I.hatZeta m) := (I.hatZeta_smooth m).continuous
  have hshift : Continuous
      (Ingredients.hatZetaML I m (lIdx β I.Λ m k)) := by
    unfold Ingredients.hatZetaML shiftCutoff
    exact hhat.comp (continuous_id.sub continuous_const)
  have hzeta : Continuous (I.zetaMK m k) := by
    unfold Ingredients.zetaMK scaledCutoff
    exact I.zeta_smooth.continuous.comp
      ((continuous_id.sub continuous_const).div_const (tau β I.Λ m))
  unfold Ingredients.zetaProd
  exact hshift.mul hzeta

theorem zetaProd_hasCompactSupport {β : ℝ} (I : Ingredients β)
    {m : ℕ} (k : ℤ) : HasCompactSupport (I.zetaProd m k) := by
  unfold Ingredients.zetaProd
  exact HasCompactSupport.mul_left
    (f := Ingredients.hatZetaML I m (lIdx β I.Λ m k))
    (f' := I.zetaMK m k) (CorrTimeRegularity.zetaMK_hasCompactSupport I k)

/-- Each mode's temporal forcing is continuous and compactly supported. -/
theorem zetaProd_exp_continuous_compactSupport {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) :
    Continuous (fun s => I.zetaProd m k s *
      Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * s)) ∧
    HasCompactSupport (fun s => I.zetaProd m k s *
      Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * s)) := by
  constructor
  · exact (zetaProd_continuous I k).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  · exact HasCompactSupport.mul_right
      (f := I.zetaProd m k) (f' := fun s =>
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * s))
      (zetaProd_hasCompactSupport I k)

/-- The `corrTime` is continuous in time for every positive-scale mode. -/
theorem corrTime_continuous {β : ℝ} (I : Ingredients β) {m : ℕ}
    (κ : ℝ) (k : ℤ) :
    Continuous (I.corrTime κ m k) := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let g : ℝ → ℝ := fun s => I.zetaProd m k s * Real.exp (ρ * s)
  have hgcont : Continuous g := by
    exact (zetaProd_continuous I k).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.mul_right (f := I.zetaProd m k)
      (f' := fun s => Real.exp (ρ * s)) (zetaProd_hasCompactSupport I k)
  have hgintegrable : Integrable g := hgcont.integrable_of_hasCompactSupport hgcompact
  have hIic (t : ℝ) : IntegrableOn g (Set.Iic t) := hgintegrable.integrableOn
  have hprimitive : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s) := by
    exact (intervalIntegral.continuous_primitive
      (fun a b => hgcont.intervalIntegrable a b) 0)
  have hIic_eq (t : ℝ) :
      (∫ s in Set.Iic t, g s) = (∫ s in Set.Iic 0, g s) +
        ∫ s in (0 : ℝ)..t, g s := by
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (μ := volume) (f := g) (hIic 0) (hIic t)
    linarith only [hsub]
  have hmemory_eq (t : ℝ) : I.corrTime κ m k t = Real.exp (-ρ * t) *
      ∫ s in Set.Iic t, g s := by
    unfold Ingredients.corrTime
    rw [show (fun s => I.zetaProd m k s * Real.exp (ρ * (s - t))) =
        fun s => Real.exp (-ρ * t) * g s by
          funext s
          dsimp [g]
          rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring,
            Real.exp_add]
          ring]
    rw [integral_const_mul]
  have hcontH : Continuous (fun t : ℝ => ∫ s in Set.Iic t, g s) := by
    have heq : (fun t : ℝ => ∫ s in Set.Iic t, g s) =
        fun t => (∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..t, g s := by
      funext t
      exact hIic_eq t
    rw [heq]
    exact continuous_const.add hprimitive
  rw [show I.corrTime κ m k = fun t => Real.exp (-ρ * t) *
      (∫ s in Set.Iic t, g s) by
        funext t
        exact hmemory_eq t]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hcontH

/-- Smoothness of a single-mode forcing in the cutoff data. -/
theorem zetaProd_contDiff {β : ℝ} (I : Ingredients β) {m : ℕ} (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (I.zetaProd m k) := by
  have hhat : ContDiff ℝ (⊤ : ℕ∞)
      (Ingredients.hatZetaML I m (lIdx β I.Λ m k)) := by
    unfold Ingredients.hatZetaML shiftCutoff
    exact (I.hatZeta_smooth m).comp (contDiff_id.sub contDiff_const)
  have hzeta : ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k) := by
    unfold Ingredients.zetaMK scaledCutoff
    exact I.zeta_smooth.comp
      ((contDiff_id.sub contDiff_const).div_const (tau β I.Λ m))
  unfold Ingredients.zetaProd
  exact hhat.mul hzeta

theorem CorrTimeRegularity.corrTime_eq_exp_mul_Iic {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) :
    I.corrTime κ m k = fun t =>
      Real.exp (-((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)) * t) *
        (∫ s in Set.Iic t, I.zetaProd m k s *
          Real.exp ((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * s)) := by
  funext t
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let g : ℝ → ℝ := fun s => I.zetaProd m k s * Real.exp (ρ * s)
  unfold Ingredients.corrTime
  rw [show (fun s => I.zetaProd m k s * Real.exp (ρ * (s - t))) =
      fun s => Real.exp (-ρ * t) * g s by
        funext s
        dsimp [g]
        rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring,
          Real.exp_add]
        ring]
  rw [integral_const_mul]

/-- The explicit memory coefficient solves its scalar relaxation ODE. -/
theorem corrTime_hasDerivAt {β : ℝ} (I : Ingredients β) {m : ℕ}
    (κ : ℝ) (k : ℤ) (t : ℝ) :
    HasDerivAt (I.corrTime κ m k)
      (I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t) t := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let g : ℝ → ℝ := fun s => I.zetaProd m k s * Real.exp (ρ * s)
  have hgcont : Continuous g := by
    exact (zetaProd_continuous I k).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.mul_right (f := I.zetaProd m k)
      (f' := fun s => Real.exp (ρ * s)) (zetaProd_hasCompactSupport I k)
  have hgintegrable : Integrable g := hgcont.integrable_of_hasCompactSupport hgcompact
  have hIic (r : ℝ) : IntegrableOn g (Set.Iic r) := hgintegrable.integrableOn
  have hIic_eq (r : ℝ) :
      (∫ s in Set.Iic r, g s) = (∫ s in Set.Iic 0, g s) +
        ∫ s in (0 : ℝ)..r, g s := by
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (μ := volume) (f := g) (hIic 0) (hIic r)
    linarith only [hsub]
  have hprim : HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, g s) (g t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hgcont.intervalIntegrable 0 t
    · exact hgcont.stronglyMeasurableAtFilter volume (𝓝 t)
    · exact hgcont.continuousAt
  let E := Real.exp (-ρ * t)
  let H := (∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..t, g s
  have hcancel : E * Real.exp (ρ * t) = 1 := by
    dsimp [E]
    rw [← Real.exp_add]
    have hsum : -ρ * t + ρ * t = 0 := by ring
    rw [hsum, Real.exp_zero]
  have hFval : I.corrTime κ m k t = E * H := by
    have heq := congrFun (CorrTimeRegularity.corrTime_eq_exp_mul_Iic I (m := m) κ k) t
    change I.corrTime κ m k t = E * H
    rw [heq]
    dsimp [E, H, ρ, g]
    rw [hIic_eq t]
  have harg : HasDerivAt (fun r : ℝ => -ρ * r) (-ρ) t := by
    simpa using (hasDerivAt_const_mul (-ρ) : HasDerivAt (fun r => -ρ * r) (-ρ) t)
  have hexp := (Real.hasDerivAt_exp (-ρ * t)).comp t harg
  have hsum := hprim.const_add (∫ s in Set.Iic 0, g s)
  have hprodRaw := hexp.mul hsum
  have hprod : HasDerivAt (fun r : ℝ => Real.exp (-ρ * r) *
      ((∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..r, g s))
      (E * (-ρ) * H + E * g t) t := by
    convert hprodRaw using 1
    · rfl
    · simp only [Function.comp_apply]
      dsimp [E, H]
  have hval : E * (-ρ) * H + E * g t =
      I.zetaProd m k t - ρ * I.corrTime κ m k t := by
    rw [hFval, show g t = I.zetaProd m k t * Real.exp (ρ * t) by rfl]
    calc
      E * (-ρ) * H + E * (I.zetaProd m k t * Real.exp (ρ * t)) =
          (-ρ * E) * H + I.zetaProd m k t *
            (E * Real.exp (ρ * t)) := by ring
      _ = I.zetaProd m k t - ρ * (E * H) := by rw [hcancel]; ring
  have hbase := hprod.congr_deriv hval
  have hrepr : I.corrTime κ m k = fun r =>
      Real.exp (-ρ * r) *
        ((∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..r, g s) := by
    funext r
    rw [CorrTimeRegularity.corrTime_eq_exp_mul_Iic I (m := m) κ k]
    change Real.exp (-ρ * r) * (∫ s in Set.Iic r, g s) =
      Real.exp (-ρ * r) *
        ((∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..r, g s)
    rw [hIic_eq r]
  convert hbase using 1

/-- The memory integral is C² in time; this is enough for the joint C²
regularity of the single-mode corrector. -/
theorem corrTime_contDiff_two {β : ℝ} (I : Ingredients β) {m : ℕ}
    (κ : ℝ) (k : ℤ) : ContDiff ℝ 2 (I.corrTime κ m k) := by
  have hcont : Continuous (I.corrTime κ m k) := corrTime_continuous I κ k
  have hforcing : ContDiff ℝ (⊤ : ℕ∞) (I.zetaProd m k) := zetaProd_contDiff I k
  have hdiff : Differentiable ℝ (I.corrTime κ m k) := by
    intro t
    exact (corrTime_hasDerivAt I κ k t).differentiableAt
  have hderivEq : deriv (I.corrTime κ m k) = fun t =>
      I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t := by
    funext t
    exact (corrTime_hasDerivAt I κ k t).deriv
  have hderivCont : Continuous (deriv (I.corrTime κ m k)) := by
    rw [hderivEq]
    exact hforcing.continuous.sub
      (continuous_const.mul hcont)
  have hC1 : ContDiff ℝ 1 (I.corrTime κ m k) :=
    contDiff_one_iff_deriv.mpr ⟨hdiff, hderivCont⟩
  have hderivC1 : ContDiff ℝ 1 (deriv (I.corrTime κ m k)) := by
    rw [hderivEq]
    have hforcing1 : ContDiff ℝ 1 (I.zetaProd m k) :=
      hforcing.of_le (by norm_num)
    let ρ : ℝ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
    have hconstant : ContDiff ℝ 1 (fun _ : ℝ => ρ) := contDiff_const
    have hscaled : ContDiff ℝ 1
        (fun t => ρ * I.corrTime κ m k t) := hconstant.mul hC1
    exact hforcing1.sub hscaled
  have hC2 : ContDiff ℝ ((1 : ℕ∞ω) + 1) (I.corrTime κ m k) := by
    rw [contDiff_succ_iff_deriv]
    exact ⟨hdiff, by norm_num, hderivC1⟩
  convert hC2 using 1
  all_goals norm_num

end AVenhance.Infra.Section3
