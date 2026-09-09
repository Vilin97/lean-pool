/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicIntegration
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
