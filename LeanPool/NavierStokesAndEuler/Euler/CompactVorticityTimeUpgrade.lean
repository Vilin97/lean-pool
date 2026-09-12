/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerClassicalClass
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import LeanPool.NavierStokesAndEuler.Euler.WeakTimeContinuity
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time regularity from the projected weak equation

Uniform bounds for the genuine spatial Sobolev norms upgrade strong `L²`
continuity to continuity of every spatial jet. This is the interpolation
step in the Comparator bridge. In particular, its higher Sobolev
continuity conclusion is not assumed in any of its hypotheses.
-/

section

/-!
# Upgrading an equation tested against a dense set

These Hilbert-space lemmas separate the time regularity argument from the PDE.
Uniform bounds for scalar derivatives against dense test vectors imply strong
Lipschitz continuity. Only scalar continuity is required at the time endpoints.
Likewise, an integral equation on dense tests determines the vector-valued
integral equation and hence its strong derivative when the right-hand side is
continuous.
-/

@[expose] public section

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
  · intro t ht
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

end
end

end

@[expose] public section

noncomputable section

namespace Euler.ComparatorBridge

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerOrdinarySobolev
  EulerSmoothSobolev Finset
open scoped ContDiff Topology NNReal

/-- A recovered smooth-`L²` representative inherits the Comparator's weak
time continuity. No continuity of its higher derivatives is used here. -/
theorem comparator_weak_pairings_continuous
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ}
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ t, (A t).field = (v · (t : ℝ))) (φ : L2) :
    Continuous (fun t => inner ℝ φ (A t).toLp) := by
  let ι : Icc (0 : ℝ) T → Ici (0 : ℝ) := fun t => ⟨t, t.property.1⟩
  have hi : Continuous ι := continuous_subtype_val.subtype_mk _
  have he (t : Icc (0 : ℝ) T) : (A t).toLp = h.velocityLp (ι t) := by
    apply Lp.ext
    filter_upwards [(A t).toLp_ae,
      (h.velocity_memLp (t : ℝ) t.property.1).coeFn_toLp] with x hx hy
    exact hx.trans ((congrFun (hA t) x).trans hy.symm)
  simpa only [Function.comp_def, ← he] using (h.velocityLp_weakly_continuous φ).comp hi

/-- The Comparator's classical divergence constraint gives the genuine
Hilbert-space solenoidal constraint on every recovered velocity slice. -/
theorem comparator_velocity_mem_solenoidal
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ}
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ t, (A t).field = (v · (t : ℝ))) (t : Icc (0 : ℝ) T) :
    (A t).toLp ∈ solenoidalSpace := by
  apply smooth_mem_solenoidal (A t).field (A t).smooth (A t).memLp
  intro x
  rw [hA t]
  exact h.div_free x t t.property.1

/-- The actual tensor Sobolev norm of a difference is controlled by the
sum of the two actual norms. -/
theorem tensorNorm_fieldSub_le (A B : SmoothL2Field Space) (q : ℕ) :
    tensorNorm q (fieldSub A B) ≤ tensorNorm q A + tensorNorm q B := by
  simp only [tensorNorm, jetLp_fieldSub, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun n _ => norm_sub_le _ _)

/-- A fixed jet is bounded by the finite tensor norm containing it. -/
theorem jetLp_norm_le_tensorNorm (A : SmoothL2Field Space) (q : ℕ) :
    ‖A.jetLp q‖ ≤ tensorNorm q A := by
  exact Finset.single_le_sum (fun n _ => norm_nonneg (A.jetLp n))
    (Finset.mem_range.mpr (Nat.lt_succ_self q))

/-- Per-order jet bounds give the finite tensor bounds used below. -/
theorem tensorNorm_uniform_of_jetLp_uniform
    {K : Type*} (A : K → SmoothL2Field Space)
    (hb : ∀ n : ℕ, ∃ M : ℝ, ∀ t, ‖(A t).jetLp n‖ ≤ M) :
    ∀ q : ℕ, ∃ M : ℝ, ∀ t, tensorNorm q (A t) ≤ M := by
  classical
  intro q
  refine ⟨∑ n ∈ Finset.range (q + 1), (hb n).choose, ?_⟩
  intro t
  exact Finset.sum_le_sum (fun n _ => (hb n).choose_spec t)

/-- Strong `L²` continuity plus uniform higher spatial Sobolev bounds
implies continuity of every actual spatial `L²` jet. -/
theorem jetLp_continuous_of_toLp_continuous
    {K : Type*} [TopologicalSpace K] (A : K → SmoothL2Field Space)
    (h0 : Continuous (fun t => (A t).toLp))
    (hb : ∀ q : ℕ, ∃ M : ℝ, ∀ t, tensorNorm q (A t) ≤ M) :
    ∀ q : ℕ, Continuous (fun t => (A t).jetLp q) := by
  intro q
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨M, hM⟩ := hb (2 * q)
  have hbound (t : K) : WordBound (2 * q) (M + M) (fieldSub (A t) (A s)) := by
    intro n hn w
    apply (wordBound_tensorNorm (2 * q) (fieldSub (A t) (A s)) n hn w).trans
    exact (tensorNorm_fieldSub_le (A t) (A s) (2 * q)).trans
      (add_le_add (hM t) (hM s))
  have hi (t : K) : ‖(A t).jetLp q - (A s).jetLp q‖ ≤
      wordCount q * Real.sqrt (‖(A t).toLp - (A s).toLp‖ * (M + M)) := by
    rw [← jetLp_fieldSub]
    exact (jetLp_norm_le_tensorNorm (fieldSub (A t) (A s)) q).trans
      (by simpa only [toLp_fieldSub] using
        tensorNorm_interpolate_zero (fieldSub (A t) (A s)) q (M + M) (hbound t))
  have ht : Tendsto (fun t => ‖(A t).toLp - (A s).toLp‖) (𝓝 s) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp h0.continuousAt
  apply squeeze_zero (fun _ => norm_nonneg _) hi
  simpa only [zero_mul, Real.sqrt_zero, mul_zero] using
    ((ht.mul_const (M + M)).sqrt.const_mul (wordCount q))

/-- A bounded spatial `H²` norm bounds the projected Euler right-hand
side in `L²`. This estimate does not use time regularity. -/
theorem projectedRhs_norm_le_of_tensorNorm_le
    (A : SmoothL2Field Space) (M : ℝ) (hM : tensorNorm 2 A ≤ M) :
    ‖(projectedRhs A).toLp‖ ≤ 39 * smoothEmbeddingConstant * M ^ 2 := by
  have hM0 : 0 ≤ M := (tensorNorm_nonneg 2 A).trans hM
  have hw : WordBound 2 M A := fun n hn w =>
    (wordBound_tensorNorm 2 A n hn w).trans hM
  rw [projectedRhs_toLp, norm_neg]
  apply (solenoidalProjection_apply_norm_le _).trans
  apply (advection_norm_velocity A A ((13 * smoothEmbeddingConstant) * M)
    (wordBound_pointwise hw)).trans
  have hc : 0 ≤ (13 * smoothEmbeddingConstant) * M :=
    mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM0
  exact (mul_le_mul_of_nonneg_left
    (wordBound_derivative hw (by norm_num : 1 ≤ 2)) hc).trans_eq (by ring)

/-- Uniform spatial bounds supply a uniform bound for the projected
right-hand side even before strong time continuity has been established. -/
theorem projectedRhs_uniform_bound
    {K : Type*} (A : K → SmoothL2Field Space)
    (hb : ∃ M : ℝ, ∀ t, tensorNorm 2 (A t) ≤ M) :
    ∃ C : ℝ≥0, ∀ t, ‖(projectedRhs (A t)).toLp‖ ≤ C := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨⟨39 * smoothEmbeddingConstant * M ^ 2, ?_⟩, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg)
      (sq_nonneg M)
  · intro t
    exact projectedRhs_norm_le_of_tensorNorm_le (A t) M (hM t)

/-- A projected Euler equation tested against a dense family is enough to
recover the development's full scalar-pressure class. The hypotheses require
only weak time continuity and uniform spatial bounds; both strong `L²` time
regularity and continuity of every higher spatial Sobolev norm are proved. -/
theorem isSmoothScalarEuler_of_weak_projectedEquation
    {T : ℝ} (hT : 0 < T) (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hs : ∀ t, (A t).toLp ∈ solenoidalSpace)
    (hb : ∀ q : ℕ, ∃ M : ℝ, ∀ t, tensorNorm q (A t) ≤ M)
    (D : Set solenoidalSpace) (hD : Dense D)
    (hc : ∀ φ ∈ D, Continuous (fun t => inner ℝ (φ : L2) (A t).toLp))
    (hd : ∀ φ ∈ D, ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => inner ℝ (φ : L2) (A (projIcc 0 T hT.le r)).toLp)
        (inner ℝ (φ : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp) t) :
    IsSmoothScalarEuler (hT := hT.le) A := by
  let u : ℝ → solenoidalSpace := fun r =>
    ⟨(A (projIcc 0 T hT.le r)).toLp, hs _⟩
  have hbs (t : Icc (0 : ℝ) T) :
      (projectedRhs (A t)).toLp ∈ solenoidalSpace := by
    rw [projectedRhs_toLp]
    exact solenoidalSpace.neg_mem (solenoidalProjection_mem _)
  let b : ℝ → solenoidalSpace := fun r =>
    ⟨(projectedRhs (A (projIcc 0 T hT.le r))).toLp, hbs _⟩
  have huc : ∀ φ ∈ D, ContinuousOn (fun r => inner ℝ φ (u r)) (Icc 0 T) := by
    intro φ hφ
    exact ((hc φ hφ).comp continuous_projIcc).continuousOn
  have hud : ∀ φ ∈ D, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun r => inner ℝ φ (u r)) (inner ℝ φ (b t)) t := by
    intro φ hφ t ht
    change HasDerivAt
      (fun r => inner ℝ (φ : L2) (A (projIcc 0 T hT.le r)).toLp)
      (inner ℝ (φ : L2) (projectedRhs (A (projIcc 0 T hT.le t))).toLp) t
    rw [projIcc_of_mem hT.le ⟨ht.1.le, ht.2.le⟩]
    exact hd φ hφ t ht
  obtain ⟨C, hC⟩ := projectedRhs_uniform_bound A (hb 2)
  have hl : LipschitzOnWith C u (Icc 0 T) :=
    WeakHilbertODE.lipschitzOnWith_of_dense_weak_equation hD hT C huc hud
      (fun t _ => hC (projIcc 0 T hT.le t))
  have hu : Continuous (fun t : Icc (0 : ℝ) T => u t) :=
    continuousOn_iff_continuous_domRestrict.mp hl.continuousOn
  have h0 : Continuous (fun t => (A t).toLp) := by
    apply (continuous_subtype_val.comp hu).congr
    intro t
    change (A (projIcc 0 T hT.le (t : ℝ))).toLp = (A t).toLp
    rw [projIcc_of_mem hT.le t.property]
  have hA := jetLp_continuous_of_toLp_continuous A h0 hb
  have hbc : Continuous b := by
    apply Continuous.subtype_mk
    exact (continuous_toLp (fun t => projectedRhs (A t))
      (projectedRhs_continuous A hA 0)).comp continuous_projIcc
  apply (scalarEuler_iff_projected A).mpr
  refine ⟨hA, hs, ?_⟩
  intro t ht
  have hdu := WeakHilbertODE.hasDerivAt_of_dense_weak_equation
    hD huc hbc.continuousOn hud ht
  have h := solenoidalSpace.subtypeL.hasFDerivAt.comp_hasDerivAt t hdu
  change HasDerivAt (fun r => (A (projIcc 0 T hT.le r)).toLp)
    (projectedRhs (A (projIcc 0 T hT.le t))).toLp t at h
  rw [projIcc_of_mem hT.le ⟨ht.1.le, ht.2.le⟩] at h
  exact h

end Euler.ComparatorBridge
