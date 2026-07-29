/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaEqDigamma
public import LeanPool.Odlyzko.ExplicitFormula.TartarPoitouTransform
public import LeanPool.Odlyzko.Numerics.Integrability
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Archimedean Kernel

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A fermi dirac kernel used in the Odlyzko-bound argument. -/
noncomputable def fermiDiracKernel (x : ℝ) : ℝ :=
  1 / (Real.exp x + 1)

/-- An inverse gauss kernel used in the Odlyzko-bound argument. -/
noncomputable def inverseGaussKernel (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.exp (-x) - 2 * f x / (Real.exp x + 1)) /
    (1 - Real.exp (-x))

theorem inverseGaussKernel_eq
    {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    inverseGaussKernel f x =
      (1 - f x) / Real.sinh x - fermiDiracKernel x := by
  have hexp : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hexpm1 : Real.exp x - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hx))
  have hexpp1 : Real.exp x + 1 ≠ 0 := by positivity
  have hsinh_formula :
      Real.sinh x =
        (Real.exp x ^ 2 - 1) / (2 * Real.exp x) := by
    rw [Real.sinh_eq, Real.exp_neg]
    grind
  unfold inverseGaussKernel fermiDiracKernel
  rw [hsinh_formula, Real.exp_neg]
  grind

private theorem fermiDiracKernel_nonneg (x : ℝ) :
    0 ≤ fermiDiracKernel x := by
  unfold fermiDiracKernel
  positivity

private theorem fermiDiracKernel_le_exp_neg (x : ℝ) :
    fermiDiracKernel x ≤ Real.exp (-x) := by
  unfold fermiDiracKernel
  rw [one_div, Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos x)
    (le_add_of_nonneg_right zero_le_one)

theorem integrableOn_fermiDiracKernel_Ioi :
    IntegrableOn fermiDiracKernel (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
  · exact
      (by
        unfold fermiDiracKernel
        have hden :
            ∀ x : ℝ, Real.exp x + 1 ≠ 0 :=
          fun x ↦ ne_of_gt (by positivity)
        exact
          (continuous_const :
            Continuous (fun _ : ℝ ↦ (1 : ℝ))).div
            (Real.continuous_exp.add continuous_const) hden :
          Continuous fermiDiracKernel)
        |>.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (fermiDiracKernel_nonneg x)]
    exact fermiDiracKernel_le_exp_neg x

theorem integral_fermiDiracKernel :
    (∫ x : ℝ in Ioi 0, fermiDiracKernel x) =
      Real.log 2 := by
  let F : ℝ → ℝ :=
    fun x ↦ (-1 : ℝ) * Real.log (1 + Real.exp (-x))
  have hderiv :
      ∀ x ∈ Ici (0 : ℝ),
        HasDerivAt F (fermiDiracKernel x) x := by
    intro x hx
    have he :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hsum :=
      (hasDerivAt_const x (1 : ℝ)).add he
    have hpos : 0 < 1 + Real.exp (-x) := by positivity
    have hlog :=
      (hsum.log hpos.ne').const_mul (-1 : ℝ)
    have hvalue :
        fermiDiracKernel x =
          -(-Real.exp (-x) / (1 + Real.exp (-x))) := by
      unfold fermiDiracKernel
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    rw [hvalue]
    simpa only [F, Pi.add_apply, Function.comp_apply,
      zero_add, mul_neg, mul_one, neg_one_mul] using hlog
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-x))
        atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
    have hone :
        Tendsto (fun x : ℝ ↦ 1 + Real.exp (-x))
          atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hexp
    simpa [F] using
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hone).neg
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv integrableOn_fermiDiracKernel_Ioi hlim
  (convert h using 1; norm_num [F])

end NumberField.Odlyzko
