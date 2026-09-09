/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

/-!
# Upgrading an equation tested against a dense set

These Hilbert-space lemmas separate the time regularity argument from the PDE.
Uniform bounds for scalar derivatives against dense test vectors imply strong
Lipschitz continuity. Only scalar continuity is required at the time endpoints.
Likewise, an integral equation on dense tests determines the vector-valued
integral equation and hence its strong derivative when the right-hand side is
continuous.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal

namespace Euler.WeakHilbertODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A norm bound tested on a dense subset is a norm bound in the Hilbert space. -/
theorem norm_le_of_dense_inner_bound {D : Set H} (hD : Dense D)
    {z : H} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ ∈ D, ‖inner ℝ φ z‖ ≤ C * ‖φ‖) : ‖z‖ ≤ C := by
  have hall : ∀ φ : H, ‖inner ℝ φ z‖ ≤ C * ‖φ‖ := by
    intro φ
    exact hD.induction hbound
      (isClosed_le (continuous_id.inner continuous_const).norm
        (continuous_const.mul continuous_norm)) φ
  have hz := hall z
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hz
  nlinarith [norm_nonneg z]

/-- Dense scalar testing determines a vector uniquely. -/
theorem eq_of_dense_inner_eq {D : Set H} (hD : Dense D) {x y : H}
    (heq : ∀ φ ∈ D, inner ℝ φ x = inner ℝ φ y) : x = y := by
  have hz : ‖x - y‖ ≤ 0 := norm_le_of_dense_inner_bound hD le_rfl (by
    intro φ hφ
    simp [inner_sub_right, heq φ hφ])
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- Bounded scalar derivatives on the open interval give a strong Lipschitz
bound on the closed interval. No strong continuity of the path is assumed. -/
theorem lipschitzOnWith_of_dense_scalar_derivative
    {D : Set H} (hD : Dense D) {u : ℝ → H} {a c : ℝ} (hac : a < c)
    (C : ℝ≥0)
    (hcont : ∀ φ ∈ D, ContinuousOn (fun t => inner ℝ φ (u t)) (Icc a c))
    (hderiv : ∀ φ ∈ D, ∀ t ∈ Ioo a c,
      ∃ d : ℝ, HasDerivAt (fun s => inner ℝ φ (u s)) d t ∧
        ‖d‖ ≤ (C : ℝ) * ‖φ‖) :
    LipschitzOnWith C u (Icc a c) := by
  have hscalar (φ : H) (hφ : φ ∈ D) :
      LipschitzOnWith (C * ‖φ‖₊) (fun t => inner ℝ φ (u t)) (Icc a c) := by
    have hopen : LipschitzOnWith (C * ‖φ‖₊)
        (fun t => inner ℝ φ (u t)) (Ioo a c) := by
      apply (convex_Ioo a c).lipschitzOnWith_of_nnnorm_deriv_le
      · intro t ht
        exact (hderiv φ hφ t ht).choose_spec.1.differentiableAt
      · intro t ht
        obtain ⟨d, hd, hdb⟩ := hderiv φ hφ t ht
        rw [hd.deriv]
        exact_mod_cast hdb
    have hclosure := hopen.closure (by simpa [closure_Ioo hac.ne] using hcont φ hφ)
    simpa [closure_Ioo hac.ne] using hclosure
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro t ht s hs
  apply norm_le_of_dense_inner_bound hD (mul_nonneg C.coe_nonneg (norm_nonneg _))
  intro φ hφ
  have hb := (lipschitzOnWith_iff_norm_sub_le.mp (hscalar φ hφ)) ht hs
  simpa only [inner_sub_right, NNReal.coe_mul, coe_nnnorm, mul_right_comm] using hb

/-- Strong continuity follows from weak scalar equations with uniformly
bounded derivatives, including at the endpoints. -/
theorem continuousOn_of_dense_scalar_derivative
    {D : Set H} (hD : Dense D) {u : ℝ → H} {a c : ℝ} (hac : a < c)
    (C : ℝ≥0)
    (hcont : ∀ φ ∈ D, ContinuousOn (fun t => inner ℝ φ (u t)) (Icc a c))
    (hderiv : ∀ φ ∈ D, ∀ t ∈ Ioo a c,
      ∃ d : ℝ, HasDerivAt (fun s => inner ℝ φ (u s)) d t ∧
        ‖d‖ ≤ (C : ℝ) * ‖φ‖) :
    ContinuousOn u (Icc a c) :=
  (lipschitzOnWith_of_dense_scalar_derivative hD hac C hcont hderiv).continuousOn

/-- A bounded vector right-hand side provides the scalar derivative bounds. -/
theorem lipschitzOnWith_of_dense_weak_equation
    {D : Set H} (hD : Dense D) {u b : ℝ → H} {a c : ℝ} (hac : a < c)
    (C : ℝ≥0)
    (hcont : ∀ φ ∈ D, ContinuousOn (fun t => inner ℝ φ (u t)) (Icc a c))
    (hderiv : ∀ φ ∈ D, ∀ t ∈ Ioo a c,
      HasDerivAt (fun s => inner ℝ φ (u s)) (inner ℝ φ (b t)) t)
    (hbound : ∀ t ∈ Ioo a c, ‖b t‖ ≤ C) :
    LipschitzOnWith C u (Icc a c) := by
  apply lipschitzOnWith_of_dense_scalar_derivative hD hac C hcont
  intro φ hφ t ht
  refine ⟨inner ℝ φ (b t), hderiv φ hφ t ht, ?_⟩
  calc
    ‖inner ℝ φ (b t)‖ ≤ ‖φ‖ * ‖b t‖ := norm_inner_le_norm _ _
    _ ≤ ‖φ‖ * C := mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg _)
    _ = (C : ℝ) * ‖φ‖ := mul_comm _ _

variable [CompleteSpace H]

/-- Dense scalar integral identities imply the vector integral identity. -/
theorem sub_eq_integral_of_dense_pairing
    {D : Set H} (hD : Dense D) {u b : ℝ → H} {a t : ℝ}
    (hb : IntervalIntegrable b volume a t)
    (hweak : ∀ φ ∈ D,
      inner ℝ φ (u t) - inner ℝ φ (u a) = ∫ s in a..t, inner ℝ φ (b s)) :
    u t - u a = ∫ s in a..t, b s := by
  apply eq_of_dense_inner_eq hD
  intro φ hφ
  rw [inner_sub_right, hweak φ hφ]
  exact (innerSL ℝ φ).intervalIntegral_comp_comm hb

/-- Scalar integral identities supply strong continuity without a prior
strong measurability or continuity assumption on the path itself. -/
theorem continuousOn_of_dense_integral_equation
    {D : Set H} (hD : Dense D) {u b : ℝ → H} {a c : ℝ}
    (hb : IntervalIntegrable b volume a c)
    (hweak : ∀ t ∈ Icc a c, ∀ φ ∈ D,
      inner ℝ φ (u t) - inner ℝ φ (u a) = ∫ s in a..t, inner ℝ φ (b s)) :
    ContinuousOn u (Icc a c) := by
  have hprimitive : ContinuousOn (fun t => ∫ s in a..t, b s) (Icc a c) :=
    (intervalIntegral.continuousOn_primitive_interval' hb left_mem_uIcc).mono Icc_subset_uIcc
  apply (continuousOn_const.add hprimitive).congr
  intro t ht
  have htint := hb.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc ht))
  have heq := sub_eq_integral_of_dense_pairing hD htint (hweak t ht)
  exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)

/-- Continuous right-hand sides give a strong derivative of a path satisfying
the integral equation on dense tests, including one-sided endpoint derivatives. -/
theorem hasDerivWithinAt_of_dense_integral_equation
    {D : Set H} (hD : Dense D) {u b : ℝ → H} {a c t : ℝ}
    (hb : ContinuousOn b (Icc a c)) (ht : t ∈ Icc a c)
    (hweak : ∀ s ∈ Icc a c, ∀ φ ∈ D,
      inner ℝ φ (u s) - inner ℝ φ (u a) = ∫ r in a..s, inner ℝ φ (b r)) :
    HasDerivWithinAt u (b t) (Icc a c) t := by
  have hac : a ≤ c := ht.1.trans ht.2
  have hbi : IntervalIntegrable b volume a c := hb.intervalIntegrable_of_Icc hac
  have hbt : IntervalIntegrable b volume a t :=
    hbi.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc ht))
  let : Fact (t ∈ Icc a c) := ⟨ht⟩
  have hprimitive : HasDerivWithinAt (fun s => ∫ r in a..s, b r)
      (b t) (Icc a c) t :=
    intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a c) (t := Icc a c)
      hbt (hb.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hb t ht)
  apply (hprimitive.const_add (u a)).congr_of_mem _ ht
  intro s hs
  have hbs := hbi.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc hs))
  have heq := sub_eq_integral_of_dense_pairing hD hbs (hweak s hs)
  exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)

/-- Weak derivatives against a dense set and continuity of the vector
right-hand side imply the exact vector integral equation. -/
theorem sub_eq_integral_of_dense_weak_equation
    {D : Set H} (hD : Dense D) {u b : ℝ → H} {a c t : ℝ}
    (hu : ∀ φ ∈ D, ContinuousOn (fun s => inner ℝ φ (u s)) (Icc a c))
    (hb : ContinuousOn b (Icc a c))
    (hderiv : ∀ φ ∈ D, ∀ s ∈ Ioo a c,
      HasDerivAt (fun r => inner ℝ φ (u r)) (inner ℝ φ (b s)) s)
    (ht : t ∈ Icc a c) : u t - u a = ∫ s in a..t, b s := by
  have hsub : Icc a t ⊆ Icc a c := Icc_subset_Icc_right ht.2
  apply sub_eq_integral_of_dense_pairing hD
    ((hb.mono hsub).intervalIntegrable_of_Icc ht.1)
  intro φ hφ
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 ((hu φ hφ).mono hsub)
  · intro s hs
    exact hderiv φ hφ s ⟨hs.1, hs.2.trans_le ht.2⟩
  · exact (continuousOn_const.inner (hb.mono hsub)).intervalIntegrable_of_Icc ht.1

/-- A weak Hilbert-space ODE with a continuous right-hand side is a strong
ODE. It is enough to test on a dense set; the path need not be known to be
strongly continuous or strongly measurable beforehand. -/
theorem hasDerivWithinAt_of_dense_weak_equation
    {D : Set H} (hD : Dense D) {u b : ℝ → H} {a c t : ℝ}
    (hu : ∀ φ ∈ D, ContinuousOn (fun s => inner ℝ φ (u s)) (Icc a c))
    (hb : ContinuousOn b (Icc a c))
    (hderiv : ∀ φ ∈ D, ∀ s ∈ Ioo a c,
      HasDerivAt (fun r => inner ℝ φ (u r)) (inner ℝ φ (b s)) s)
    (ht : t ∈ Icc a c) : HasDerivWithinAt u (b t) (Icc a c) t := by
  apply hasDerivWithinAt_of_dense_integral_equation hD hb ht
  intro s hs φ _
  rw [← inner_sub_right, sub_eq_integral_of_dense_weak_equation hD hu hb hderiv hs]
  symm
  exact (innerSL ℝ φ).intervalIntegral_comp_comm
    ((hb.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)

/-- Interior-point form of the strong derivative supplied by the weak ODE. -/
theorem hasDerivAt_of_dense_weak_equation
    {D : Set H} (hD : Dense D) {u b : ℝ → H} {a c t : ℝ}
    (hu : ∀ φ ∈ D, ContinuousOn (fun s => inner ℝ φ (u s)) (Icc a c))
    (hb : ContinuousOn b (Icc a c))
    (hderiv : ∀ φ ∈ D, ∀ s ∈ Ioo a c,
      HasDerivAt (fun r => inner ℝ φ (u r)) (inner ℝ φ (b s)) s)
    (ht : t ∈ Ioo a c) : HasDerivAt u (b t) t :=
  (hasDerivWithinAt_of_dense_weak_equation hD hu hb hderiv (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end Euler.WeakHilbertODE
