/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.NavierStokes.AxisPreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedPeriodicAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Basic
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicIntegration
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Mixed candidate assembly from primitive axis zero germs

Potential increments may be arbitrary physical fields.  Their local axis zero
germs replace the copy-potential representation used by the original consumer.
All raw estimates, finite residual estimates, shrinking support and finite
endpoint-extension obligations remain unchanged.  The diagonal schedule, axis
blow-up, infinite residual limits and candidate consequences are derived.
-/

section

/-!
# Consequences of the actual candidate fields

No candidate existence is asserted here.  The first results use precisely
`CandidateProperties`.  Force derivatives at initial time are taken within the
physical future half-space.  For the actual globally smooth constructed force
these are proved equal to its ordinary full derivatives.
-/

section

/-!
# A concrete periodic H³ supremum bound

Coordinate fundamental-theorem-of-calculus estimates are iterated over the
unit cube. All derivatives below are the ordinary Frechet coordinate
derivatives on `ProblemStatement.Space`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace

namespace NavierStokes.PeriodicSobolev

open ProblemStatement PeriodicIntegration

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- Replace coord, given by `x + (s - x i) • coordinateVector i`. -/
def replaceCoord (i : Fin 3) (x : Space) (s : ℝ) : Space :=
  x + (s - x i) • coordinateVector i

@[simp] theorem replaceCoord_apply (i j : Fin 3) (x : Space) (s : ℝ) :
    replaceCoord i x s j = if j = i then s else x j := by
  by_cases h : j = i
  · subst j
    simp [replaceCoord, coordinateVector]
  · simp [replaceCoord, coordinateVector, h]

@[simp] theorem replaceCoord_self (i : Fin 3) (x : Space) :
    replaceCoord i x (x i) = x := by simp [replaceCoord]

theorem continuous_replaceCoord (i : Fin 3) :
    Continuous (fun z : Space × ℝ => replaceCoord i z.1 z.2) :=
  continuous_fst.add ((continuous_snd.sub
    ((EuclideanSpace.proj i).continuous.comp continuous_fst)).smul continuous_const)

theorem hasDerivAt_replaceCoord (i : Fin 3) (x : Space) (s : ℝ) :
    HasDerivAt (replaceCoord i x) (coordinateVector i) s := by
  convert! (hasDerivAt_const s x).add
    (((hasDerivAt_id s).sub_const (x i)).smul_const (coordinateVector i)) using 1
  simp []

/-- Unit interval averaging after replacing one coordinate. -/
def average (i : Fin 3) (h : Space → ℝ) (x : Space) : ℝ :=
  ∫ s in Icc (0 : ℝ) 1, h (replaceCoord i x s)

theorem average_eq_interval (i : Fin 3) (h : Space → ℝ) (x : Space) :
    average i h x = ∫ s in (0 : ℝ)..1, h (replaceCoord i x s) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact (setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))).symm

theorem continuous_average {h : Space → ℝ} (hh : Continuous h) (i : Fin 3) :
    Continuous (average i h) :=
  continuous_parametric_integral_of_continuous
    (f := fun x s => h (replaceCoord i x s)) (hh.comp (continuous_replaceCoord i)) isCompact_Icc

theorem average_nonneg {h : Space → ℝ} (hh : ∀ x, 0 ≤ h x) (i : Fin 3) (x : Space) :
    0 ≤ average i h x := integral_nonneg fun s => hh (replaceCoord i x s)

theorem average_mono_on_curve {h k : Space → ℝ} (hh : Continuous h) (hk : Continuous k)
    (i : Fin 3) (x : Space)
    (hle : ∀ s ∈ Icc (0 : ℝ) 1, h (replaceCoord i x s) ≤ k (replaceCoord i x s)) :
    average i h x ≤ average i k x := by
  have hc : Continuous (replaceCoord i x) :=
    (continuous_replaceCoord i).comp (continuous_const.prodMk continuous_id)
  exact setIntegral_mono_on (hh.comp hc).integrableOn_Icc (hk.comp hc).integrableOn_Icc
    measurableSet_Icc hle

theorem average_add {h k : Space → ℝ} (hh : Continuous h) (hk : Continuous k)
    (i : Fin 3) (x : Space) :
    average i (fun y => h y + k y) x = average i h x + average i k x := by
  have hc : Continuous (replaceCoord i x) :=
    (continuous_replaceCoord i).comp (continuous_const.prodMk continuous_id)
  exact integral_add (hh.comp hc).integrableOn_Icc (hk.comp hc).integrableOn_Icc

theorem average_const_mul (a : ℝ) (h : Space → ℝ) (i : Fin 3) (x : Space) :
    average i (fun y => a * h y) x = a * average i h x := integral_const_mul _ _

private theorem scalar_le_average_add_average_bound
    {f f' h : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f') (hh : Continuous h)
    (hd : ∀ s, HasDerivAt f (f' s) s) (hb : ∀ s, |f' s| ≤ h s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x ≤ (∫ s in (0 : ℝ)..1, f s) + ∫ s in (0 : ℝ)..1, h s := by
  have hn : ∀ s, 0 ≤ h s := fun s => (abs_nonneg (f' s)).trans (hb s)
  have hdiff : ∀ y ∈ Icc (0 : ℝ) 1,
      f x - f y ≤ ∫ s in (0 : ℝ)..1, h s := by
    intro y hy
    rcases le_total y x with hyx | hxy
    · calc
        f x - f y = ∫ s in y..x, f' s :=
          (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
            (hf'.intervalIntegrable _ _)).symm
        _ ≤ ∫ s in y..x, h s := intervalIntegral.integral_mono_on hyx
          (hf'.intervalIntegrable _ _) (hh.intervalIntegrable _ _)
          (fun s _ => (le_abs_self _).trans (hb s))
        _ ≤ ∫ s in (0 : ℝ)..1, h s := intervalIntegral.integral_mono_interval hy.1 hyx hx.2
          (Eventually.of_forall hn) (hh.intervalIntegrable _ _)
    · have heq : (∫ s in x..y, -f' s) = f x - f y := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s _ => hd s) (hf'.intervalIntegrable _ _)]
        ring
      calc
        f x - f y = ∫ s in x..y, -f' s := heq.symm
        _ ≤ ∫ s in x..y, h s := intervalIntegral.integral_mono_on hxy
          (hf'.neg.intervalIntegrable _ _) (hh.intervalIntegrable _ _)
          (fun s _ => (neg_le_abs _).trans (hb s))
        _ ≤ ∫ s in (0 : ℝ)..1, h s := intervalIntegral.integral_mono_interval hx.1 hxy hy.2
          (Eventually.of_forall hn) (hh.intervalIntegrable _ _)
  have havg := intervalIntegral.integral_mono_on (zero_le_one : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f x) volume 0 1)
    ((hf.fun_add continuous_const).intervalIntegrable _ _ :
      IntervalIntegrable (fun y => f y + ∫ s in (0 : ℝ)..1, h s) volume 0 1)
    (fun y hy => by linarith [hdiff y hy])
  simpa [intervalIntegral.integral_add (hf.intervalIntegrable _ _) intervalIntegrable_const] using
      havg

private theorem curve_energy_bound {f f' : ℝ → Space}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ s, HasDerivAt f (f' s) s) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖f x‖ ^ 2 ≤ 2 * ((∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) +
      ∫ s in (0 : ℝ)..1, ‖f' s‖ ^ 2) := by
  have hcross (s : ℝ) : |2 * ⟪f s, f' s⟫_ℝ| ≤ ‖f s‖ ^ 2 + ‖f' s‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hinner := abs_real_inner_le_norm (f s) (f' s)
    nlinarith [sq_nonneg (‖f s‖ - ‖f' s‖)]
  have hh := scalar_le_average_add_average_bound (hf.norm.fun_pow 2)
    (continuous_const.mul (hf.inner hf')) ((hf.norm.fun_pow 2).fun_add (hf'.norm.fun_pow 2))
    (fun s => (hd s).norm_sq) hcross hx
  rw [intervalIntegral.integral_add ((hf.norm.fun_pow 2).intervalIntegrable _ _)
    ((hf'.norm.fun_pow 2).intervalIntegrable _ _)] at hh
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) (zero_le_one : (0 : ℝ) ≤ 1)
    (fun s => sq_nonneg ‖f' s‖)
  linarith

/-- Sq field, given by `‖f x‖ ^ 2`. -/
def sqField (f : Space → Space) (x : Space) : ℝ := ‖f x‖ ^ 2

theorem continuous_sqField {f : Space → Space} (hf : Continuous f) : Continuous (sqField f) :=
  hf.norm.fun_pow 2

theorem line_energy_bound {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (x : Space) (hx : x i ∈ Icc (0 : ℝ) 1) :
    sqField f x ≤ 2 * (average i (sqField f) x + average i (sqField (spatialPartial i f)) x) := by
  have hc : Continuous (replaceCoord i x) :=
    (continuous_replaceCoord i).comp (continuous_const.prodMk continuous_id)
  have hd : ∀ s, HasDerivAt (fun r => f (replaceCoord i x r))
      (spatialPartial i f (replaceCoord i x s)) s := by
    intro s
    exact (hf.differentiable (by simp) (replaceCoord i x s)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_replaceCoord i x s)
  have h := curve_energy_bound (hf.continuous.comp hc)
    ((PeriodicUniqueness.spatial_partial_contDiff hf i).continuous.comp hc) hd hx
  rw [average_eq_interval, average_eq_interval]
  simpa only [Function.comp_apply, replaceCoord_self, sqField, spatialPartial] using h

theorem averaged_line_energy_bound {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (hji : j ≠ i) (x : Space) (hx : x j ∈ Icc (0 : ℝ) 1) :
    average i (sqField f) x ≤ 2 *
      (average i (average j (sqField f)) x +
        average i (average j (sqField (spatialPartial j f))) x) := by
  have hc := continuous_sqField hf.continuous
  have hcd := continuous_sqField (PeriodicUniqueness.spatial_partial_contDiff hf j).continuous
  have ha := continuous_average hc j
  have hb := continuous_average hcd j
  have hm := average_mono_on_curve hc (continuous_const.fun_mul (ha.fun_add hb)) i x
    (fun s _ => line_energy_bound hf j (replaceCoord i x s)
      (by simpa only [replaceCoord_apply, ite_eq_right hji] using hx))
  rw [average_const_mul, average_add ha hb] at hm
  exact hm

theorem twice_averaged_line_energy_bound {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (x : Space) (hx : x k ∈ Icc (0 : ℝ) 1) :
    average i (average j (sqField f)) x ≤ 2 *
      (average i (average j (average k (sqField f))) x +
        average i (average j (average k (sqField (spatialPartial k f)))) x) := by
  have hc := continuous_sqField hf.continuous
  have hcd := continuous_sqField (PeriodicUniqueness.spatial_partial_contDiff hf k).continuous
  have ha := continuous_average (continuous_average hc k) j
  have hb := continuous_average (continuous_average hcd k) j
  have hm := average_mono_on_curve (continuous_average hc j)
    (continuous_const.fun_mul (ha.fun_add hb)) i x
    (fun s _ => averaged_line_energy_bound hf j k hkj (replaceCoord i x s)
      (by simpa only [replaceCoord_apply, ite_eq_right hki] using hx))
  rw [average_const_mul, average_add ha hb] at hm
  exact hm

/-- Cube point, given by `toSpace ![a, b, c]`. -/
def cubePoint (a b c : ℝ) : Space := toSpace ![a, b, c]

/-- An explicit iterated product Lebesgue integral on the unit cube. -/
def boxIntegral (h : Space → ℝ) : ℝ :=
  ∫ a in Icc (0 : ℝ) 1, ∫ b in Icc (0 : ℝ) 1, ∫ c in Icc (0 : ℝ) 1,
    h (cubePoint a b c)

theorem averages_eq_boxIntegral (h : Space → ℝ) (x : Space) :
    average 0 (average 1 (average 2 h)) x = boxIntegral h := by
  unfold average boxIntegral
  apply integral_congr_ae
  filter_upwards with a
  apply integral_congr_ae
  filter_upwards with b
  apply integral_congr_ae
  filter_upwards with c
  congr 1
  ext i
  fin_cases i <;> simp [cubePoint]

theorem boxIntegral_nonneg {h : Space → ℝ} (hh : ∀ x, 0 ≤ h x) : 0 ≤ boxIntegral h := by
  unfold boxIntegral
  apply integral_nonneg
  intro a
  apply integral_nonneg
  intro b
  apply integral_nonneg
  intro c
  exact hh _

/-- The eight mixed derivatives with each coordinate used at most once.
Every derivative here has total order at most three. -/
def mixedEnergy (f : Space → Space) : ℝ :=
  boxIntegral (sqField f) +
  boxIntegral (sqField (spatialPartial 0 f)) +
  boxIntegral (sqField (spatialPartial 1 f)) +
  boxIntegral (sqField (spatialPartial 2 f)) +
  boxIntegral (sqField (spatialPartial 1 (spatialPartial 0 f))) +
  boxIntegral (sqField (spatialPartial 2 (spatialPartial 0 f))) +
  boxIntegral (sqField (spatialPartial 2 (spatialPartial 1 f))) +
  boxIntegral (sqField (spatialPartial 2 (spatialPartial 1 (spatialPartial 0 f))))

theorem mixedEnergy_nonneg (f : Space → Space) : 0 ≤ mixedEnergy f := by
  unfold mixedEnergy
  repeat' apply add_nonneg
  all_goals exact boxIntegral_nonneg (fun x => sq_nonneg _)

/-- Three successive coordinate FTC estimates. No periodicity is needed for
the estimate at a point already in the closed unit cube. -/
theorem norm_sq_le_eight_mixedEnergy_on_cube {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (x : Space) (hx : ∀ i : Fin 3, x i ∈ Icc (0 : ℝ) 1) :
    ‖f x‖ ^ 2 ≤ 8 * mixedEnergy f := by
  have hd0 : ContDiff ℝ ∞ (spatialPartial 0 f) :=
    PeriodicUniqueness.spatial_partial_contDiff hf 0
  have hd1 : ContDiff ℝ ∞ (spatialPartial 1 f) :=
    PeriodicUniqueness.spatial_partial_contDiff hf 1
  have hd10 : ContDiff ℝ ∞ (spatialPartial 1 (spatialPartial 0 f)) :=
    PeriodicUniqueness.spatial_partial_contDiff hd0 1
  have h0 := line_energy_bound hf 0 x (hx 0)
  have h1 := averaged_line_energy_bound hf 0 1 (by decide) x (hx 1)
  have h10 := averaged_line_energy_bound hd0 0 1 (by decide) x (hx 1)
  have h2 := twice_averaged_line_energy_bound hf 0 1 2 (by decide) (by decide) x (hx 2)
  have h20 := twice_averaged_line_energy_bound hd0 0 1 2 (by decide) (by decide) x (hx 2)
  have h21 := twice_averaged_line_energy_bound hd1 0 1 2 (by decide) (by decide) x (hx 2)
  have h210 := twice_averaged_line_energy_bound hd10 0 1 2 (by decide) (by decide) x (hx 2)
  simp only [averages_eq_boxIntegral] at h2 h20 h21 h210
  change sqField f x ≤ _
  unfold mixedEnergy
  linarith

/-- The pointwise estimate on all of space follows by an explicitly proved
integer-lattice reduction to the cube. -/
theorem norm_sq_le_eight_mixedEnergy {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f) (x : Space) :
    ‖f x‖ ^ 2 ≤ 8 * mixedEnergy f := by
  obtain ⟨y, hy, hfy⟩ := PeriodicUniqueness.exists_cube_representative
    (fun i z => hp z i) x
  have h := norm_sq_le_eight_mixedEnergy_on_cube hf y hy
  rwa [hfy] at h

/-- A derivative definition of the H³ energy. Every ordered coordinate
derivative of order two and three is included, as are the zeroth and all
first derivatives. The selected mixed derivatives have an extra copy;
these fixed positive multiplicities only change the choice of H³ norm. -/
def derivativeH3Energy (f : Space → Space) : ℝ :=
  mixedEnergy f +
    (∑ i : Fin 3, ∑ j : Fin 3,
      boxIntegral (sqField (spatialPartial i (spatialPartial j f)))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      boxIntegral (sqField (spatialPartial i (spatialPartial j (spatialPartial k f)))))

/-- Derivative H3 norm, given by `Real.sqrt (derivativeH3Energy f)`. -/
def derivativeH3Norm (f : Space → Space) : ℝ := Real.sqrt (derivativeH3Energy f)

theorem mixedEnergy_le_derivativeH3Energy (f : Space → Space) :
    mixedEnergy f ≤ derivativeH3Energy f := by
  have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      boxIntegral (sqField (spatialPartial i (spatialPartial j f))) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact boxIntegral_nonneg (fun x => sq_nonneg _)
  have h3 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      boxIntegral (sqField (spatialPartial i (spatialPartial j (spatialPartial k f)))) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact boxIntegral_nonneg (fun x => sq_nonneg _)
  unfold derivativeH3Energy
  linarith

theorem derivativeH3Energy_nonneg (f : Space → Space) : 0 ≤ derivativeH3Energy f :=
  (mixedEnergy_nonneg f).trans (mixedEnergy_le_derivativeH3Energy f)

theorem derivativeH3Norm_nonneg (f : Space → Space) : 0 ≤ derivativeH3Norm f :=
  Real.sqrt_nonneg _

/-- A concrete H³-to-supremum estimate with the harmless numerical constant 3. -/
theorem norm_le_three_derivativeH3Norm {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f) (x : Space) :
    ‖f x‖ ≤ 3 * derivativeH3Norm f := by
  have hpoint := norm_sq_le_eight_mixedEnergy hf hp x
  have hdom := mixedEnergy_le_derivativeH3Energy f
  have hnonneg := derivativeH3Energy_nonneg f
  have hsqrt := Real.sq_sqrt hnonneg
  have hs : ‖f x‖ ^ 2 ≤ (3 * derivativeH3Norm f) ^ 2 := by
    unfold derivativeH3Norm
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (derivativeH3Norm_nonneg f))).mp hs

/-- Derivative H3 unbounded at one, given by `∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, t ∈ Ioo
(1 - δ) 1 ∧ M < derivativeH3Norm (fun x => u (t, x))`. -/
def DerivativeH3UnboundedAtOne (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, t ∈ Ioo (1 - δ) 1 ∧ M < derivativeH3Norm (fun x => u (t, x))

/-- Pointwise speed blow-up forces unbounded H³ norm arbitrarily close to
time one, by the proved embedding rather than an assumed Sobolev theorem. -/
theorem speed_unbounded_implies_derivativeH3_unbounded {u : VelocityField}
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u) (hb : SpeedUnboundedAtOne u) :
    DerivativeH3UnboundedAtOne u := by
  intro M hM δ hδ
  have hd : 0 < min δ 1 := lt_min hδ zero_lt_one
  obtain ⟨t, x, ht, hx⟩ := hb (3 * M) (by positivity) (min δ 1) hd
  have ht0 : 0 < t := by have hm := min_le_right δ (1 : ℝ); linarith [ht.1]
  have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht0.le, ht.2⟩
  have hn := norm_le_three_derivativeH3Norm (hu t ht') (hp t ht') x
  refine ⟨t, ⟨?_, ht.2⟩, ?_⟩
  · have hm := min_le_left δ (1 : ℝ)
    linarith [ht.1]
  · linarith

/-- The candidate specification therefore entails the explicitly defined
H³ norm blow-up condition, without asserting existence of a candidate. -/
theorem candidate_derivativeH3_unbounded {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) : DerivativeH3UnboundedAtOne u := by
  apply speed_unbounded_implies_derivativeH3_unbounded ?_ h.velocity_periodic h.speed_unbounded
  intro t ht
  exact h.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun x => show (t, x) ∈ preSingularDomain from ⟨ht, mem_univ x⟩)

end NavierStokes.PeriodicSobolev

end
end

end

section

/-!
# Conditional maximal classical lifespan of the candidate

An actual `CandidateProperties` witness has maximal classical lifespan one.
The proof uses the proved periodic uniqueness theorem and a compactness bound
for a continuous periodic field across time one. It assumes no general
Navier--Stokes existence theorem and never identifies pressure gauges.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology ContDiff

namespace NavierStokes.MaximalLifespan

open ProblemStatement PeriodicIntegration

/-- Lifespan domain, given by `Ico 0 T ×ˢ univ`. -/
noncomputable def lifespanDomain (T : ℝ) : Set SpaceTime := Ico 0 T ×ˢ univ

/-- A finite, positive classical lifespan for the exact viscosity-one PDE.
The initial datum is an actual spatial velocity field. Pressures are retained
as witnesses but are never required to agree with a different gauge. -/
structure ClassicalSolution (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) : Prop where
  lifespan_pos : 0 < T
  velocity_smooth : ContDiffOn ℝ ∞ u (lifespanDomain T)
  pressure_smooth : ContDiffOn ℝ ∞ p (lifespanDomain T)
  velocity_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) p
  initial_velocity : ∀ x : Space, u (0, x) = initial x
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    navierStokesResidual u p t x = f (t, x)

/-- Velocity agrees on, given by `∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x)`. -/
noncomputable def VelocityAgreesOn (T : ℝ) (u v : VelocityField) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x)

/-- An extension has a strictly larger time interval and preserves the
velocity on the entire original interval. Its pressure may have a different
time-dependent spatially constant normalization. -/
noncomputable def HasClassicalExtension (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) : Prop :=
  ∃ S : ℝ, ∃ v : VelocityField, ∃ q : PressureField,
    T < S ∧ ClassicalSolution f initial S v q ∧ VelocityAgreesOn T u v

/-- Is maximal classical solution, given by `ClassicalSolution f initial T u p ∧
¬HasClassicalExtension f initial T u`. -/
noncomputable def IsMaximalClassicalSolution (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) : Prop :=
  ClassicalSolution f initial T u p ∧ ¬HasClassicalExtension f initial T u

/-- The actual set of finite positive times supported by classical solutions
for the fixed force and initial datum. No existence is built into the definition. -/
noncomputable def admissibleLifespans (f : VelocityField) (initial : Space → Space) : Set ℝ :=
  {T | ∃ u : VelocityField, ∃ p : PressureField, ClassicalSolution f initial T u p}

theorem ClassicalSolution.restrict {f : VelocityField} {initial : Space → Space}
    {S T : ℝ} {u : VelocityField} {p : PressureField}
    (h : ClassicalSolution f initial T u p) (hS : 0 < S) (hST : S ≤ T) :
    ClassicalSolution f initial S u p := by
  have hsub : lifespanDomain S ⊆ lifespanDomain T := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_le hST⟩, hz.2⟩
  refine ⟨hS, h.velocity_smooth.mono hsub, h.pressure_smooth.mono hsub, ?_, ?_,
    h.initial_velocity, ?_, ?_⟩
  · intro t ht x i
    exact h.velocity_periodic t ⟨ht.1, ht.2.trans_le hST⟩ x i
  · intro t ht x i
    exact h.pressure_periodic t ⟨ht.1, ht.2.trans_le hST⟩ x i
  · intro t ht x
    exact h.divergence_free t ⟨ht.1, ht.2.trans_le hST⟩ x
  · intro t ht x
    exact h.navier_stokes t ⟨ht.1, ht.2.trans_le hST⟩ x

/-- Any two actual classical solutions agree on their common interval.
This is derived by restriction to each compact subinterval and the proved
energy uniqueness theorem. Only velocity equality is asserted. -/
theorem ClassicalSolution.agree_on_overlap {f : VelocityField} {initial : Space → Space}
    {T S : ℝ} {u v : VelocityField} {p q : PressureField}
    (hu : ClassicalSolution f initial T u p) (hv : ClassicalSolution f initial S v q) :
    VelocityAgreesOn (min T S) u v := by
  intro t ht x
  have htT : t < T := (lt_min_iff.mp ht.2).1
  have htS : t < S := (lt_min_iff.mp ht.2).2
  have hsubT : PeriodicUniqueness.slab 0 t ⊆ lifespanDomain T := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt htT⟩, hz.2⟩
  have hsubS : PeriodicUniqueness.slab 0 t ⊆ lifespanDomain S := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt htS⟩, hz.2⟩
  have hcompact : ∀ r ∈ Icc (0 : ℝ) t, ∀ y : Space, u (r, y) = v (r, y) := by
    apply PeriodicUniqueness.classical_uniqueness_on_Icc
      (hu.velocity_smooth.mono hsubT) (hv.velocity_smooth.mono hsubS)
      (hu.pressure_smooth.mono hsubT) (hv.pressure_smooth.mono hsubS)
    · intro r hr y i
      exact hu.velocity_periodic r ⟨hr.1, hr.2.trans_lt htT⟩ y i
    · intro r hr y i
      exact hv.velocity_periodic r ⟨hr.1, hr.2.trans_lt htS⟩ y i
    · intro r hr y i
      exact hu.pressure_periodic r ⟨hr.1, hr.2.trans_lt htT⟩ y i
    · intro r hr y i
      exact hv.pressure_periodic r ⟨hr.1, hr.2.trans_lt htS⟩ y i
    · intro r hr y
      exact hu.divergence_free r ⟨hr.1.le, hr.2.trans htT⟩ y
    · intro r hr y
      exact hv.divergence_free r ⟨hr.1.le, hr.2.trans htS⟩ y
    · intro r hr y
      exact hu.navier_stokes r ⟨hr.1, hr.2.trans htT⟩ y
    · intro r hr y
      exact hv.navier_stokes r ⟨hr.1, hr.2.trans htS⟩ y
    · intro y
      exact (hu.initial_velocity y).trans (hv.initial_velocity y).symm
  exact hcompact t ⟨ht.1, le_rfl⟩ x

theorem candidate_is_classical_solution {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    ClassicalSolution f (fun _ => 0) 1 u p :=
  ⟨zero_lt_one, h.velocity_smooth, h.pressure_smooth, h.velocity_periodic,
    h.pressure_periodic, h.zero_initial_velocity, h.divergence_free, h.navier_stokes⟩

theorem candidate_agree_on_overlap {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f (fun _ => 0) T v q) :
    VelocityAgreesOn (min T 1) v u :=
  hv.agree_on_overlap (candidate_is_classical_solution h)

/-- Compactness bounds a relatively continuous periodic field on an entire
closed time slab, uniformly over all spatial points. -/
theorem periodic_bound_on_slab {V : Type*} [NormedAddCommGroup V]
    {g : SpaceTime → V} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ (univ : Set Space)))
    (hperiod : UnitSpatialPeriodsOn (Icc a b) g) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x : Space, ‖g (t, x)‖ ≤ B := by
  have hK : IsCompact (toSpace '' cube) :=
    (show IsCompact cube from isCompact_Icc).image toSpace.continuous
  have hgK : ContinuousOn g (Icc a b ×ˢ (toSpace '' cube)) :=
    hg.mono (fun z hz => ⟨hz.1, mem_univ z.2⟩)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hgK
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht x
  obtain ⟨z, hz, hzx⟩ := PeriodicUniqueness.exists_cube_representative
    (f := fun y : Space => g (t, y)) (fun i y => hperiod t ht y i) x
  have hzK : z ∈ toSpace '' cube := by
    refine ⟨toSpace.symm z, ?_, toSpace.apply_symm_apply z⟩
    exact ⟨fun i => (hz i).1, fun i => (hz i).2⟩
  calc
    ‖g (t, x)‖ = ‖g (t, z)‖ := congrArg norm hzx.symm
    _ ≤ B := hB (t, z) ⟨ht, hzK⟩
    _ ≤ max B 1 := le_max_left _ _

/-- Unbounded speed rules out even a continuous periodic extension through
time one, once agreement with the original field is known. -/
theorem unbounded_excludes_continuous_extension {u v : VelocityField}
    (h : SpeedUnboundedAtOne u)
    (hv : ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ (univ : Set Space)))
    (hpv : UnitSpatialPeriodsOn (Icc (0 : ℝ) 1) v)
    (hagrees : VelocityAgreesOn 1 u v) : False := by
  obtain ⟨B, _, hB⟩ := periodic_bound_on_slab hv hpv
  apply unbounded_speed_excludes_uniform_bound h
  refine ⟨B, ?_⟩
  intro t ht x
  rw [hagrees t ht x]
  exact hB t ⟨ht.1, ht.2.le⟩ x

/-- No classical solution for the same force and datum can have lifespan
larger than one. Uniqueness supplies the required pre-one agreement. -/
theorem candidate_no_solution_after_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f) (hT : 1 < T)
    (hv : ClassicalSolution f (fun _ => 0) T v q) : False := by
  have hsub : Icc (0 : ℝ) 1 ×ˢ (univ : Set Space) ⊆ lifespanDomain T := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩
  apply unbounded_excludes_continuous_extension h.speed_unbounded
    (hv.velocity_smooth.continuousOn.mono hsub)
  · intro t ht x i
    exact hv.velocity_periodic t ⟨ht.1, ht.2.trans_lt hT⟩ x i
  · intro t ht x
    exact (candidate_agree_on_overlap h hv t
      ⟨ht.1, lt_min (ht.2.trans hT) ht.2⟩ x).symm

theorem candidate_all_lifespans_le_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f (fun _ => 0) T v q) : T ≤ 1 := by
  by_contra hnot
  exact candidate_no_solution_after_one h (lt_of_not_ge hnot) hv

/-- The given lifespan-one solution is maximal under extension of its
velocity. No literal equality between pressure representatives is required. -/
theorem candidate_is_maximal {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    IsMaximalClassicalSolution f (fun _ => 0) 1 u p := by
  refine ⟨candidate_is_classical_solution h, ?_⟩
  rintro ⟨T, v, q, hT, hv, _⟩
  exact candidate_no_solution_after_one h hT hv

/-- Any shorter classical solution extends by the actual candidate field. -/
theorem candidate_extends_shorter_solution {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f (fun _ => 0) T v q) (hT : T < 1) :
    HasClassicalExtension f (fun _ => 0) T v := by
  refine ⟨1, u, p, hT, candidate_is_classical_solution h, ?_⟩
  simpa only [min_eq_left hT.le] using candidate_agree_on_overlap h hv

/-- Every maximal classical solution for these data has exactly lifespan one. -/
theorem maximal_lifespan_eq_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : IsMaximalClassicalSolution f (fun _ => 0) T v q) : T = 1 := by
  have hle := candidate_all_lifespans_le_one h hv.1
  apply le_antisymm hle
  by_contra hnot
  exact hv.2 (candidate_extends_shorter_solution h hv.1 (lt_of_not_ge hnot))

/-- There is a greatest admissible finite classical lifespan, and it is one.
Existence at that time comes solely from the supplied candidate witness. -/
theorem candidate_greatest_lifespan {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    IsGreatest (admissibleLifespans f (fun _ => 0)) 1 := by
  refine ⟨⟨u, p, candidate_is_classical_solution h⟩, ?_⟩
  rintro T ⟨v, q, hv⟩
  exact candidate_all_lifespans_le_one h hv

/-- The entire set of finite admissible classical lifespans is `(0,1]`. -/
theorem candidate_admissible_lifespans {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    admissibleLifespans f (fun _ => 0) = Ioc (0 : ℝ) 1 := by
  ext T
  constructor
  · rintro ⟨v, q, hv⟩
    exact ⟨hv.lifespan_pos, candidate_all_lifespans_le_one h hv⟩
  · intro ht
    exact ⟨u, p, (candidate_is_classical_solution h).restrict ht.1 ht.2⟩

/-- A global classical solution would restrict to a forbidden lifespan
greater than one. This makes the exclusion of infinite-time continuation
explicit without assuming any existence theorem. -/
theorem candidate_excludes_global_solution {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f)
    (hv : ContDiffOn ℝ ∞ v futureDomain) (hq : ContDiffOn ℝ ∞ q futureDomain)
    (hpv : UnitSpatialPeriodsOn (Ici (0 : ℝ)) v)
    (hpq : UnitSpatialPeriodsOn (Ici (0 : ℝ)) q)
    (hvzero : ∀ x : Space, v (0, x) = 0)
    (hdv : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0)
    (hNSv : ∀ t : ℝ, 0 < t → ∀ x : Space, navierStokesResidual v q t x = f (t, x)) :
    False := by
  have hsub : lifespanDomain 2 ⊆ futureDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  apply candidate_no_solution_after_one h (T := 2) (by norm_num)
  refine ⟨by norm_num, hv.mono hsub, hq.mono hsub, ?_, ?_, hvzero, ?_, ?_⟩
  · intro t ht x i
    exact hpv t ht.1 x i
  · intro t ht x i
    exact hpq t ht.1 x i
  · intro t ht x
    exact hdv t ht.1 x
  · intro t ht x
    exact hNSv t ht.1 x

theorem zero_classical_solution_of_zero_force {f : VelocityField} {T : ℝ}
    (hT : 0 < T) (hf : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, f (t, x) = 0) :
    ClassicalSolution f (fun _ => 0) T (fun _ => 0) (fun _ => 0) := by
  refine ⟨hT, contDiffOn_const, contDiffOn_const, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · intro t ht x i
    rfl
  · intro t ht x i
    rfl
  · intro t ht x
    simp [spatialDivergence, spatialDerivative]
  · intro t ht x
    exact (zero_residual t x).trans (hf t ht x).symm

/-- The specified force must be nonzero somewhere before the breakdown
time. Otherwise uniqueness identifies the candidate with the zero solution. -/
theorem candidate_force_nonzero_before_one {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, f (t, x) ≠ 0 := by
  by_contra hnot
  have hf : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space, f (t, x) = 0 := by
    intro t ht x
    by_contra hnonzero
    exact hnot ⟨t, ht, x, hnonzero⟩
  have hz := zero_classical_solution_of_zero_force zero_lt_one hf
  have hagree : VelocityAgreesOn 1 (fun _ => 0) u := by
    simpa only [min_self] using candidate_agree_on_overlap h hz
  apply unbounded_speed_excludes_uniform_bound h.speed_unbounded
  refine ⟨0, ?_⟩
  intro t ht x
  rw [← hagree t ht x]
  exact norm_zero.le

end NavierStokes.MaximalLifespan

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.CandidateConsequences

open Set Filter Function ProblemStatement
open scoped ContDiff Topology BigOperators Pointwise

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m).le

theorem future_uniqueDiff : UniqueDiffOn ℝ futureDomain :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- The physical full spacetime jet, including its one-sided value at time zero. -/
noncomputable def futureJet (f : VelocityField) (m : ℕ) :=
  iteratedFDerivWithin ℝ m f futureDomain

theorem futureJet_continuous {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (m : ℕ) :
    ContinuousOn (futureJet f m) futureDomain :=
  hf.continuousOn_iteratedFDerivWithin (nat_le_infty m) future_uniqueDiff

private theorem future_spatial_translate (e : Space) :
    ((0, e) : SpaceTime) +ᵥ futureDomain = futureDomain := by
  ext z
  change z ∈ (fun w : SpaceTime => (0, e) + w) '' futureDomain ↔ z ∈ futureDomain
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [futureDomain, mem_prod, mem_Ici, mem_univ, and_true,
      Prod.fst_add, Prod.fst_zero, zero_add] using hw
  · intro hz
    refine ⟨z - (0, e), ?_, ?_⟩
    · simpa only [futureDomain, mem_prod, mem_Ici, mem_univ, and_true,
        Prod.fst_sub, sub_zero] using hz
    · simpa only [add_comm] using sub_add_cancel z ((0, e) : SpaceTime)

theorem futureJet_periodic {f : VelocityField}
    (hp : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f) (m : ℕ) :
    UnitSpatialPeriodsOn (Ici (0 : ℝ)) (futureJet f m) := by
  intro t ht x i
  have he : EqOn (fun z : SpaceTime => f (z + (0, coordinateVector i))) f futureDomain := by
    rintro ⟨s,y⟩ hz
    simpa only [Prod.mk_add_mk, add_zero] using hp s hz.1 y i
  have hc := iteratedFDerivWithin_congr (𝕜 := ℝ) he (show (t, x) ∈ futureDomain from ⟨ht, mem_univ
      _⟩) m
  have hs := iteratedFDerivWithin_comp_add_right (𝕜 := ℝ) (f := f)
    (s := futureDomain) m (0, coordinateVector i) (t, x)
  rw [future_spatial_translate] at hs
  simpa only [futureJet, Prod.mk_add_mk, add_zero] using hs.symm.trans hc

theorem futureJet_eq_full {f : VelocityField} {t : ℝ} (ht : 0 ≤ t) (x : Space)
    (m : ℕ) (hf : ContDiffAt ℝ ∞ f (t, x)) :
    futureJet f m (t, x) = iteratedFDeriv ℝ m f (t, x) :=
  iteratedFDerivWithin_eq_iteratedFDeriv future_uniqueDiff (hf.of_le (nat_le_infty m))
    ⟨ht, mem_univ _⟩

theorem futureJet_eq_full_of_pos {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) {t : ℝ} (ht : 0 < t) (x : Space) (m : ℕ) :
    futureJet f m (t, x) = iteratedFDeriv ℝ m f (t, x) :=
  futureJet_eq_full ht.le x m
    (hf.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht) univ_mem))

/-- Compact future time support gives arbitrary polynomial decay of the
physical one-sided jets, using only future smoothness and future periodicity. -/
theorem futureJet_decay {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain)
    (hp : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f) (hs : CompactFutureTimeSupport f)
    (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖futureJet f m (t, x)‖ ≤ C * (1 + t) ^ (-K) := by
  obtain ⟨T, hT, hzero⟩ := hs
  obtain ⟨M, hM, hb⟩ := MaximalLifespan.periodic_bound_on_slab
    ((futureJet_continuous hf m).mono
      (show Icc (0 : ℝ) (T + 1) ×ˢ (univ : Set Space) ⊆ futureDomain from
        fun _ hz => ⟨hz.1.1, hz.2⟩))
    (fun t ht x i => futureJet_periodic hp m t ht.1 x i)
  let C : ℝ := M * (1 + (T + 1)) ^ K
  have hbase : 0 < 1 + (T + 1) := by linarith
  have hC : 0 < C := mul_pos hM (Real.rpow_pos_of_pos hbase K)
  refine ⟨C, hC, ?_⟩
  intro t ht x
  by_cases hsmall : t ≤ T + 1
  · have hpow : (1 + (T + 1)) ^ (-K) ≤ (1 + t) ^ (-K) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hK)
    have hcancel : C * (1 + (T + 1)) ^ (-K) = M := by
      dsimp [C]
      rw [mul_assoc, ← Real.rpow_add hbase]
      simp
    calc
      ‖futureJet f m (t, x)‖ ≤ M := hb t ⟨ht, hsmall⟩ x
      _ = C * (1 + (T + 1)) ^ (-K) := hcancel.symm
      _ ≤ C * (1 + t) ^ (-K) := mul_le_mul_of_nonneg_left hpow hC.le
  · have htpos : 0 < t := by linarith
    rw [futureJet_eq_full_of_pos hf htpos x m,
      CompactForceDecay.iteratedFDeriv_eq_zero_after hzero m (by linarith : T < t) x, norm_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)

/-- The ordinary tensor bound for the same force.  Global smoothness is
provided by the actual force constructor; negative-time periodicity is not needed. -/
theorem full_forceJet_decay {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (hf : ContDiff ℝ ∞ f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ C * (1 + t) ^ (-K) := by
  obtain ⟨C, hC, hb⟩ := futureJet_decay h.force_smooth h.force_periodic h.force_time_support m K hK
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [← futureJet_eq_full ht x m hf.contDiffAt]
  exact hb t ht x

theorem full_forceMixed_decay {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (hf : ContDiff ℝ ∞ f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
        |(iteratedFDeriv ℝ m f (t, x)
          (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
            C * (1 + t) ^ (-K) := by
  obtain ⟨C, hC, hb⟩ := full_forceJet_decay h hf m K hK
  exact ⟨C, hC, fun t ht x directions j =>
    (CompactForceDecay.mixed_component_le_full f m (t, x) directions j).trans (hb t ht x)⟩

/-- All conclusions here follow from the exact candidate properties alone. -/
structure Consequences (u : VelocityField) (p : PressureField) (f : VelocityField) : Prop where
  maximal : MaximalLifespan.IsMaximalClassicalSolution f (fun _ => 0) 1 u p
  lifespans : MaximalLifespan.admissibleLifespans f (fun _ => 0) = Ioc (0 : ℝ) 1
  h3_unbounded : PeriodicSobolev.DerivativeH3UnboundedAtOne u
  force_nonzero : ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, f (t, x) ≠ 0
  force_jet_decay : ∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ‖futureJet f m (t, x)‖ ≤ C * (1 + t) ^ (-K)

theorem consequences_of_candidate {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) : Consequences u p f :=
  ⟨MaximalLifespan.candidate_is_maximal h, MaximalLifespan.candidate_admissible_lifespans h,
    PeriodicSobolev.candidate_derivativeH3_unbounded h,
    MaximalLifespan.candidate_force_nonzero_before_one h,
    futureJet_decay h.force_smooth h.force_periodic h.force_time_support⟩

/-- Retaining one growing physical trajectory strengthens unboundedness to
a genuine limit.  No monotonicity of the velocity or its norm is assumed. -/
theorem h3_tendsto_of_speed_tendsto {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (x : ℝ → Space)
    (hx : Tendsto (fun t => ‖u (t, x t)‖) (𝓝[<] (1 : ℝ)) atTop) :
    Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun y => u (t, y)))
      (𝓝[<] (1 : ℝ)) atTop := by
  rw [tendsto_atTop]
  intro M
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  have hpre : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  filter_upwards [hx.eventually (eventually_ge_atTop (3 * M)), hpos, hpre] with t hlarge ht ht1
  have hslice := TimeLocalization.spatial_smooth_including_initial u h.velocity_smooth t ⟨ht.le,
      ht1⟩
  have hb := PeriodicSobolev.norm_le_three_derivativeH3Norm hslice
    (h.velocity_periodic t ⟨ht.le, ht1⟩) (x t)
  linarith

theorem mixed_activated_speed_tendsto {A v : VelocityField}
    (haxis : Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖)
      (𝓝[<] (1 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => ‖TimeLocalization.activatedVelocity
      (MixedPeriodicAssembly.periodicVelocity A v) (t, 0)‖) (𝓝[<] (1 : ℝ)) atTop := by
  have he : (fun t : ℝ => ‖TimeLocalization.activatedVelocity
      (MixedPeriodicAssembly.periodicVelocity A v) (t, 0)‖) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖) := by
    filter_upwards [show Ioi (3 / 4 : ℝ) ∈ 𝓝[<] (1 : ℝ) from
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))] with t ht
    rw [TimeLocalization.activatedVelocity_eq_late _ ht.le,
        MixedPeriodicAssembly.periodicVelocity_origin]
  exact haxis.congr' he.symm

/-- The exact mixed assembly inputs produce one force carrying all the
lifespan, Sobolev, and full force-jet conclusions.  Nothing is assumed about
the output force, the infinite-time PDE, or the Sobolev embedding. -/
theorem mixed_exists_force_with_consequences {A v : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hv : ContDiffOn ℝ ∞ v (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hd : ∀ t < 1, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    (hz : JointResidualLimits.VanishingJointJets (MixedPeriodicAssembly.originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖)
      (𝓝[<] (1 : ℝ)) atTop) :
    ∃ F : VelocityField,
      CandidateProperties (TimeLocalization.activatedVelocity
          (MixedPeriodicAssembly.periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      ContDiff ℝ ∞ F ∧
      Consequences (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
        TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v) (t, x)))
        (𝓝[<] (1 : ℝ)) atTop ∧
      (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
          |(iteratedFDeriv ℝ m F (t, x)
            (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
              C * (1 + t) ^ (-K)) ∧
      (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n F (1, x) =
        MixedPeriodicAssembly.boundaryLimits A v p eA ev ep x n) := by
  obtain ⟨F, hc, hF, hjet⟩ := MixedPeriodicAssembly.exists_candidate_force hA hv hp hd hz eA ev ep
      haxis
  exact ⟨F, hc, hF, consequences_of_candidate hc,
    h3_tendsto_of_speed_tendsto hc (fun _ => 0) (mixed_activated_speed_tendsto haxis),
    full_forceMixed_decay hc hF, hjet⟩

end NavierStokes.CandidateConsequences

end
end

end

section

/-!
# Retaining the actual mixed candidate and its consequences

The finite-stage inputs are exactly those of
`MixedCandidateAssembly.candidate_of_finite_stages`. The same selected
schedule supplies the actual velocity and pressure sums, their endpoint
extensions, and the force with all proved consequences.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.MixedCandidateWitness

open Set Filter ProblemStatement MixedCandidateAssembly
open JointResidualLimits (OneSidedExtension)
open scoped Topology ContDiff

universe u

/-- All properties of the single scale sequence selected from the finite
stage estimates, including smooth sums and vanishing residual jets. -/
noncomputable def SelectedSchedule (h qbig : ℝ) (A B : ℕ → VelocityField)
    (P : ℕ → PressureField) (a : ℕ → ℕ) : Prop :=
  1 ≤ a 0 ∧ (∀ j, 0 < a j) ∧ (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
    Tendsto (fun j => (a j : ℝ)) atTop atTop ∧ (∀ j, 1 / (a j : ℝ) < qbig) ∧
    MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
    JointResidualLimits.VanishingJointJets
      (MixedDiagonalResidual.residual (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B P)

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The original finite-stage inputs produce one schedule and its actual
activated fields, together with the full mixed-force conclusion. -/
theorem exists_candidate_witness_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : StageEstimates F.data.h qbig
      (potentialStages H v upper bandFloor initial stages) (LocalAngularDiagonal.rawSeries D)
      (pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig initial.field)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (stages
        j).field)
    (hDirect : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig
      (LocalAngularDiagonal.rawSeries D j))
    (hpInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig pInitial)
    (hpStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (pStages j))
    (eA : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (potentialStages H v upper bandFloor initial stages j) x))
    (eB : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (LocalAngularDiagonal.rawSeries D j) x))
    (eP : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (pressureStages H v upper bandFloor pInitial pStages j) x)) :
    let A := potentialStages H v upper bandFloor initial stages
    let B := LocalAngularDiagonal.rawSeries D
    let P := pressureStages H v upper bandFloor pInitial pStages
    ∃ a : ℕ → ℕ, SelectedSchedule F.data.h qbig A B P a ∧
      let ASum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) A
      let BSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) B
      let PSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) P
      ∃ (ea : JointResidualLimits.AwayExtensions ASum)
        (eb : JointResidualLimits.AwayExtensions BSum)
        (ep : JointResidualLimits.AwayExtensions PSum),
      ∃ forcing : VelocityField,
        CandidateProperties
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
        ContDiff ℝ ∞ forcing ∧
        CandidateConsequences.Consequences
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
        Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
          TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum) (t,
              x)))
          (𝓝[<] (1 : ℝ)) atTop ∧
        (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
          ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
            |(iteratedFDeriv ℝ m forcing (t, x)
              (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
                C * (1 + t) ^ (-K)) ∧
        (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n forcing (1, x) =
          MixedPeriodicAssembly.boundaryLimits ASum BSum PSum ea eb ep x n) := by
  let A := potentialStages H v upper bandFloor initial stages
  let B := LocalAngularDiagonal.rawSeries D
  let P := pressureStages H v upper bandFloor pInitial pStages
  obtain ⟨a, hal, hap, had, ham, hat, hgap, hs, hz⟩ :=
    E.exists_schedule F.data.h_pos F.data.h_lt_half hqbig 1
  let ar : ℕ → ℝ := fun j => (a j : ℝ)
  have ha0 : 0 < ar 0 := by
    dsimp [ar]
    exact_mod_cast hap 0
  have hamin (j : ℕ) : ar 0 ≤ ar j := by
    dsimp [ar]
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hA0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (A 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hInitial hx hxz (Classical.choice (TailGaugePotential.finalPotential_awayExtensions H v upper
          bandFloor x hx))
  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (P 0) x) := by
    intro x hx hxz
    have h := MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hpInitial hx hxz (Classical.choice ((SlowBaseEndpoint.final_fields_awayExtensions H v upper
          bandFloor).2 x hx))
    simp only [P]
    exact h
  have hB0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (B 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.extension_of_eventually_zero
      ((hDirect 0).eventually_zero F.data.h_pos F.data.h_lt_half hqbig hx hxz)
  have hAsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (A j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j
  have hPsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (P j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => simpa only [P, pressureStages_succ] using hpStages j
  have ea := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hAsupport hA0 eA
  have eb := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) (fun j _ => hDirect j) hB0 eB
  have ep := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hPsupport hP0 eP
  have hcut := LocalAngularDiagonal.spatialCut_angularSum_divergence
    F.data.h_pos F.data.h_lt_half D hat ha0 hamin (hgap 0)
  have haxis := MixedAxisPreservation.local_initialized_final_origin_blowup
    H v upper bandFloor hqbig initial stages (LocalAngularDiagonal.angularSupport D) hat
  refine ⟨a, ⟨hal, hap, had, ham, hat, hgap, hs, hz⟩, ea, eb, ep, ?_⟩
  exact CandidateConsequences.mixed_exists_force_with_consequences
    (A := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) A)
    (v := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) B)
    (p := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) P)
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz ea eb ep haxis

end ActualBase

end NavierStokes.MixedCandidateWitness

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.GermCandidateAssembly

open Set Function Filter ProblemStatement
open JointResidualLimits (OneSidedExtension)
open MixedCandidateAssembly (StageEstimates pressureStages pressureStages_zero pressureStages_succ)
open scoped Topology ContDiff

/-- A property of the actual primitive field on a local physical domain.
The zero neighborhood may depend on the point and on the stage. -/
def AxisZeroOn (Ω : Set SpaceTime) (f : VelocityField) : Prop :=
  ∀ w ∈ Ω, PhysicalGraphBounds.radialProjection w = 0 → f =ᶠ[𝓝 w] fun _ => 0

theorem AxisZeroOn.add {Ω : Set SpaceTime} {f g : VelocityField}
    (hf : AxisZeroOn Ω f) (hg : AxisZeroOn Ω g) :
    AxisZeroOn Ω (fun w => f w + g w) := by
  intro w hw ha
  filter_upwards [hf w hw ha, hg w hw ha] with y hy hz
  rw [hy, hz, add_zero]

/-- The original concrete potential-stage data supplies the new hypothesis
directly.  No regularity assertion about its copy representation is added. -/
theorem potentialStage_axisZeroOn {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (p : MixedAxisPreservation.PotentialStage h (MixedAxisPreservation.localDomain h qbig)) :
    AxisZeroOn (MixedAxisPreservation.localDomain h qbig) p.field := by
  intro w hw ha
  exact p.zero_germ hh hh1 (MixedAxisPreservation.localDomain_open hh hh1 qbig)
    hw hw.1 ha

/-- Literal supported mean-stream potentials satisfy the same local property. -/
theorem angularSupport_axisZeroOn {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (p : MixedAxisPreservation.AngularSupport (MixedAxisPreservation.localDomain h qbig)) :
    AxisZeroOn (MixedAxisPreservation.localDomain h qbig) p.field := by
  intro w hw ha
  exact p.zero_germ (MixedAxisPreservation.localDomain_open hh hh1 qbig) hw
    (MixedAxisPreservation.radius_zero_of_axis ha)

/-- The base and finite initialization retain the same zeroth cutoff. -/
noncomputable def initializedSeries (base initial : VelocityField)
    (stages : ℕ → VelocityField) : ℕ → VelocityField
  | 0 => fun w => base w + initial w
  | j + 1 => stages j

theorem initializedSeries_zero (base initial : VelocityField) (stages : ℕ → VelocityField)
    (w : SpaceTime) : initializedSeries base initial stages 0 w = base w + initial w := rfl

theorem initializedSeries_succ (base initial : VelocityField) (stages : ℕ → VelocityField)
    (j : ℕ) : initializedSeries base initial stages (j + 1) = stages j := rfl

/-- Substituting the original stage fields gives exactly the original series. -/
theorem initializedSeries_of_potentialStage {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : MixedAxisPreservation.PotentialStage h Ω)
    (stages : ℕ → MixedAxisPreservation.PotentialStage h Ω) :
    initializedSeries base initial.field (fun j => (stages j).field) =
      MixedAxisPreservation.initializedSeries base initial stages := by
  funext j w
  cases j <;> rfl

/-- Local finiteness intersects only finitely many stage-dependent zero
neighborhoods.  On the zeroth cutoff plateau the actual potential sum has
the base germ, including the finite initialization. -/
theorem potentialSum_eq_base_germ {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop)
    {q : SpaceTime → ℝ} {base initial : VelocityField} {stages : ℕ → VelocityField}
    {w : SpaceTime} (hq : ContinuousAt q w) (hpos : 0 < q w)
    (hInitial : initial =ᶠ[𝓝 w] fun _ => 0)
    (hStages : ∀ j, stages j =ᶠ[𝓝 w] fun _ => 0)
    (hsmall : |scales 0 * q w| < 1 / 2) :
    SolenoidalDiagonal.potentialSum scales q (initializedSeries base initial stages)
      =ᶠ[𝓝 w] base := by
  have hz : ∀ j : ℕ, j ≠ 0 →
      initializedSeries base initial stages j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j hj
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j
  have hsum := AxisPreservation.potentialSum_eq_first_near hs hq hpos hz
  have hc := (SmoothCutoffs.scaledCutoff_eventually_one hsmall).comp_tendsto hq
  apply hsum.trans
  filter_upwards [hc, hInitial] with y hy hi
  change SmoothCutoffs.scaledCutoff (scales 0) (q y) = 1 at hy
  change SmoothCutoffs.scaledCutoff (scales 0) (q y) • (base y + initial y) = base y
  rw [hy, one_smul, hi, add_zero]

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- Potential stages, given by `initializedSeries (TailGaugePotential.finalPotential H v upper
bandFloor) initial stages`. -/
noncomputable def potentialStages (upper : ℝ) (bandFloor : ℕ)
    (initial : VelocityField) (stages : ℕ → VelocityField) : ℕ → VelocityField :=
  initializedSeries (TailGaugePotential.finalPotential H v upper bandFloor) initial stages

/-- The actual mixed diagonal agrees at the origin with the constructed slow
base for all sufficiently late times.  Its blow-up is not an input. -/
theorem origin_eventually_base (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : 0 < qbig) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (hInitial : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStages : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    (fun t : ℝ => MixedPeriodicAssembly.velocity
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (potentialStages H v upper bandFloor initial stages))
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (LocalAngularDiagonal.rawSeries D)) (t, 0)) =ᶠ[𝓝[<] 1]
      (fun t => FinalSlowBase.velocity H v upper bandFloor (t, 0)) := by
  have hl := ((tendsto_const_nhds.mul
    (AxisPreservation.physicalQ_origin_tendsto F.data.h_pos F.data.h_lt_half)).abs :
    Tendsto (fun t : ℝ => |scales 0 * PhysicalWaveSum.physicalQ F.data.h (t, 0)|)
      (𝓝[<] 1) (𝓝 |scales 0 * 0|))
  simp only [mul_zero, abs_zero] at hl
  have hsmall := hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [MixedAxisPreservation.origin_eventually_localDomain
    F.data.h_pos F.data.h_lt_half hqbig, hsmall] with t ht hst
  have ha := MixedAxisPreservation.radialProjection_origin t
  have hsum := potentialSum_eq_base_germ
    (base := TailGaugePotential.finalPotential H v upper bandFloor) hs
    (PhysicalWaveSum.physicalQ_smoothAt F.data.h_pos F.data.h_lt_half ht.1).continuousAt
    (PhysicalWaveSum.physicalQ_pos F.data.h_pos F.data.h_lt_half ht.1)
    (hInitial (t, 0) ht ha) (fun j => hStages j (t, 0) ht ha) hst
  have hc := (SolenoidalDiagonal.spatialCurl_eventuallyEq hsum).self_of_nhds
  have hd : SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
      (LocalAngularDiagonal.rawSeries D) (t, 0) = 0 :=
    DirectAngularDiagonal.angularSum_axis scales (PhysicalWaveSum.physicalQ F.data.h)
      (fun j => (D j).scalar) t 0 rfl rfl
  change SpatialCurl.spatialCurl (SolenoidalDiagonal.potentialSum scales
    (PhysicalWaveSum.physicalQ F.data.h)
    (initializedSeries (TailGaugePotential.finalPotential H v upper bandFloor) initial stages))
      (t, 0) + _ = _
  rw [hc, hd, add_zero, TailGaugePotential.finalPotential_sameCurl H v upper bandFloor ht.1]

theorem origin_blowup (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : 0 < qbig) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (hInitial : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStages : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (potentialStages H v upper bandFloor initial stages))
      (SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ F.data.h)
        (LocalAngularDiagonal.rawSeries D)) (t, 0)‖) (𝓝[<] 1) atTop := by
  apply (FinalSlowBase.axis_tendsto H v upper bandFloor).congr'
  exact (origin_eventually_base H v upper bandFloor hqbig initial stages D hInitial hStages
      hs).symm.mono
    (fun _ ht => congrArg norm ht)

/-- This has the original finite-stage obligations, with arbitrary physical
potential increments and their primitive local axis zero germs.  It returns
the same selected schedule, exact mixed fields and full force consequences. -/
theorem exists_candidate_witness_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : StageEstimates F.data.h qbig
      (potentialStages H v upper bandFloor initial stages) (LocalAngularDiagonal.rawSeries D)
      (pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig initial)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (stages j))
    (hDirect : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig
      (LocalAngularDiagonal.rawSeries D j))
    (hpInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig pInitial)
    (hpStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (pStages j))
    (eA : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (potentialStages H v upper bandFloor initial stages j) x))
    (eB : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (LocalAngularDiagonal.rawSeries D j) x))
    (eP : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (pressureStages H v upper bandFloor pInitial pStages j) x))
    (hInitialAxis : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStagesAxis : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j)) :
    let A := potentialStages H v upper bandFloor initial stages
    let B := LocalAngularDiagonal.rawSeries D
    let P := pressureStages H v upper bandFloor pInitial pStages
    ∃ a : ℕ → ℕ, MixedCandidateWitness.SelectedSchedule F.data.h qbig A B P a ∧
      let ASum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) A
      let BSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) B
      let PSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ F.data.h) P
      ∃ (ea : JointResidualLimits.AwayExtensions ASum)
        (eb : JointResidualLimits.AwayExtensions BSum)
        (ep : JointResidualLimits.AwayExtensions PSum),
      ∃ forcing : VelocityField,
        CandidateProperties
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
        ContDiff ℝ ∞ forcing ∧
        CandidateConsequences.Consequences
          (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum))
          (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)) forcing ∧
        Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
          TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum) (t,
              x)))
          (𝓝[<] (1 : ℝ)) atTop ∧
        (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
          ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
            |(iteratedFDeriv ℝ m forcing (t, x)
              (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
                C * (1 + t) ^ (-K)) ∧
        (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n forcing (1, x) =
          MixedPeriodicAssembly.boundaryLimits ASum BSum PSum ea eb ep x n) := by
  let A := potentialStages H v upper bandFloor initial stages
  let B := LocalAngularDiagonal.rawSeries D
  let P := pressureStages H v upper bandFloor pInitial pStages
  obtain ⟨a, hal, hap, had, ham, hat, hgap, hs, hz⟩ :=
    E.exists_schedule F.data.h_pos F.data.h_lt_half hqbig 1
  let ar : ℕ → ℝ := fun j => (a j : ℝ)
  have ha0 : 0 < ar 0 := by
    dsimp [ar]
    exact_mod_cast hap 0
  have hamin (j : ℕ) : ar 0 ≤ ar j := by
    dsimp [ar]
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hA0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (A 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hInitial hx hxz (Classical.choice (TailGaugePotential.finalPotential_awayExtensions H v upper
          bandFloor x hx))
  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (P 0) x) := by
    intro x hx hxz
    have h := MixedDiagonalExtensions.initial_add_extension F.data.h_pos F.data.h_lt_half hqbig
      hpInitial hx hxz (Classical.choice ((SlowBaseEndpoint.final_fields_awayExtensions H v upper
          bandFloor).2 x hx))
    simp only [P]
    exact h
  have hB0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (B 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.extension_of_eventually_zero
      ((hDirect 0).eventually_zero F.data.h_pos F.data.h_lt_half hqbig hx hxz)
  have hAsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (A j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hStages j
  have hPsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (P j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => simpa only [P, pressureStages_succ] using hpStages j
  have ea := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hAsupport hA0 eA
  have eb := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) (fun j _ => hDirect j) hB0 eB
  have ep := MixedDiagonalExtensions.diagonal_awayExtensions_local
    F.data.h_pos F.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hPsupport hP0 eP
  have hcut := LocalAngularDiagonal.spatialCut_angularSum_divergence
    F.data.h_pos F.data.h_lt_half D hat ha0 hamin (hgap 0)
  have haxis := origin_blowup H v upper bandFloor hqbig initial stages D hInitialAxis hStagesAxis
      hat
  refine ⟨a, ⟨hal, hap, had, ham, hat, hgap, hs, hz⟩, ea, eb, ep, ?_⟩
  exact CandidateConsequences.mixed_exists_force_with_consequences
    (A := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) A)
    (v := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) B)
    (p := SolenoidalDiagonal.potentialSum ar (PhysicalWaveSum.physicalQ F.data.h) P)
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz ea eb ep haxis

/-- The manuscript's exact candidate target follows from the same primitive
finite-stage data; no separate candidate witness is assumed. -/
theorem candidate_of_finite_stages (upper : ℝ) (bandFloor : ℕ)
    {qbig C : ℝ} (hqbig : 0 < qbig)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : StageEstimates F.data.h qbig
      (potentialStages H v upper bandFloor initial stages) (LocalAngularDiagonal.rawSeries D)
      (pressureStages H v upper bandFloor pInitial pStages))
    (hInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig initial)
    (hStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (stages j))
    (hDirect : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig
      (LocalAngularDiagonal.rawSeries D j))
    (hpInitial : MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig pInitial)
    (hpStages : ∀ j, MixedDiagonalExtensions.SublevelShrinkingSupport F.data.h C qbig (pStages j))
    (eA : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (potentialStages H v upper bandFloor initial stages j) x))
    (eB : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (LocalAngularDiagonal.rawSeries D j) x))
    (eP : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * F.data.h) (x 2) < qbig → ∀ j,
      Nonempty (OneSidedExtension (pressureStages H v upper bandFloor pInitial pStages j) x))
    (hInitialAxis : AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) initial)
    (hStagesAxis : ∀ j, AxisZeroOn (MixedAxisPreservation.localDomain F.data.h qbig) (stages j)) :
    candidateStatement := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ :=
    exists_candidate_witness_of_finite_stages H v upper bandFloor hqbig initial stages D
      pInitial pStages E hInitial hStages hDirect hpInitial hpStages eA eB eP hInitialAxis
          hStagesAxis
  exact ⟨_, _, forcing, hc⟩

end ActualBase

end NavierStokes.GermCandidateAssembly
