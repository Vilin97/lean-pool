/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpLinearity
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The terminal primitive of a genuine Bochner L² time field

The derivative is the input equivalence class.  Integration of its zero extension
constructs the continuous representative, its zero terminal trace, and its
almost-everywhere derivative.  No primitive or evolution solution is assumed.
-/

@[expose] public section


noncomputable section

namespace EulerTerminalTimePrimitive

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical time representative extended by zero outside the time interval. -/
def zeroExtension (T : ℝ) (u : TimeLp T E) : ℝ → E :=
  (Icc (0 : ℝ) T).indicator u

omit [NormedSpace ℝ E] in
/-- Zero extension preserves genuine square integrability. -/
theorem zeroExtension_memLp (T : ℝ) (u : TimeLp T E) :
    MemLp (zeroExtension T u) 2 volume := by
  exact (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp u)

omit [NormedSpace ℝ E] in
/-- The finite time interval makes the zero extension Bochner integrable. -/
theorem zeroExtension_integrable (T : ℝ) (u : TimeLp T E) :
    Integrable (zeroExtension T u) volume := by
  exact (show IntegrableOn (fun t => u t) (Icc (0 : ℝ) T) volume from
    (Lp.memLp u).integrable (by norm_num)).integrable_indicator measurableSet_Icc

omit [NormedSpace ℝ E] in
/-- The zero extension is the original time field almost everywhere on its interval. -/
theorem zeroExtension_ae (T : ℝ) (u : TimeLp T E) :
    zeroExtension T u =ᵐ[timeMeasure T] fun t => u t :=
  indicator_ae_eq_restrict measurableSet_Icc

/-- The actual real-valued-time representative, with terminal value zero. -/
def realPrimitive (T : ℝ) (u : TimeLp T E) (t : ℝ) : E :=
  ∫ s in T..t, zeroExtension T u s

/-- The constructed primitive is continuous on all of real time. -/
theorem realPrimitive_continuous (T : ℝ) (u : TimeLp T E) :
    Continuous (realPrimitive T u) :=
  (zeroExtension_integrable T u).continuous_primitive T

/-- The terminal condition holds by construction. -/
@[simp] theorem realPrimitive_terminal (T : ℝ) (u : TimeLp T E) :
    realPrimitive T u T = 0 := by simp [realPrimitive]

/-- All increments are the literal Bochner integrals of the zero-extended derivative. -/
theorem realPrimitive_increment (T : ℝ) (u : TimeLp T E) (s t : ℝ) :
    realPrimitive T u t - realPrimitive T u s = ∫ r in s..t, zeroExtension T u r :=
  intervalIntegral.integral_interval_sub_left
    (zeroExtension_integrable T u).intervalIntegrable
    (zeroExtension_integrable T u).intervalIntegrable

/-- On the time interval this is exactly the terminal integral of the input field. -/
theorem realPrimitive_eq_neg_integral (T : ℝ) (u : TimeLp T E)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    realPrimitive T u t = -(∫ s in t..T, u s) := by
  rw [realPrimitive, intervalIntegral.integral_symm]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.2] at hs
  change (Icc (0 : ℝ) T).indicator (fun x => u x) s = u s
  exact Set.indicator_of_mem (show s ∈ Icc (0 : ℝ) T from ⟨ht.1.trans hs.1, hs.2⟩) _

/-- The constructed real-time representative has its genuine derivative almost everywhere. -/
theorem realPrimitive_hasDerivAt_ae_global [CompleteSpace E] (T : ℝ) (u : TimeLp T E) :
    ∀ᵐ t, HasDerivAt (realPrimitive T u) (zeroExtension T u t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (zeroExtension_integrable T u).locallyIntegrable]
    with t ht using ht T

/-- Its derivative on the time interval is the original Bochner L² field. -/
theorem realPrimitive_hasDerivAt_ae [CompleteSpace E] (T : ℝ) (u : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T, HasDerivAt (realPrimitive T u) (u t) t := by
  filter_upwards [ae_mono Measure.restrict_le_self (realPrimitive_hasDerivAt_ae_global T u),
    zeroExtension_ae T u] with t ht he
  simpa only [he] using ht

/-- The genuine continuous path on the prescribed time interval. -/
def primitivePath (T : ℝ) (u : TimeLp T E) : C(Icc (0 : ℝ) T, E) :=
  ⟨fun t => realPrimitive T u t, (realPrimitive_continuous T u).comp continuous_subtype_val⟩

/-- Cauchy--Schwarz for a square-integrable scalar function on an interval. -/
theorem integral_sq_le_length_mul (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun t => (g t) ^ 2) volume a b) :
    (∫ t in a..b, g t)^2 ≤ (b-a)*(∫ t in a..b, (g t)^2) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let c := (∫ t in a..b, g t)/(b-a)
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab.le
    (fun t _ => sq_nonneg (g t-c))
  have he : (fun t => (g t-c)^2) = (fun t => (g t)^2-2*c*g t+c^2) := by
    funext t
    ring
  rw [he, intervalIntegral.integral_add (hg2.sub (hg.const_mul (2*c)))
    intervalIntegrable_const, intervalIntegral.integral_sub hg2 (hg.const_mul (2*c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [smul_eq_mul] at hn
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hc : c*(b-a) = ∫ t in a..b, g t := div_mul_cancel₀ _ hlen.ne'
  have hp := mul_nonneg hlen.le hn
  nlinarith [sq_nonneg ((b-a)*(∫ t in a..b, g t))]

/-- Bochner Cauchy--Schwarz, requiring actual square integrability rather than continuity. -/
theorem norm_integral_sq_le_length_mul (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a b) :
    ‖∫ t in a..b, f t‖^2 ≤ (b-a)*(∫ t in a..b, ‖f t‖^2) := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) hab
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (integral_sq_le_length_mul (fun t => ‖f t‖) hab hf.norm hf2)

omit [NormedSpace ℝ E] in
/-- The squared norm of the zero extension is integrable on all of real time. -/
theorem zeroExtension_norm_sq_integrable (T : ℝ) (u : TimeLp T E) :
    Integrable (fun t => ‖zeroExtension T u t‖^2) volume :=
  (zeroExtension_memLp T u).integrable_norm_pow (by norm_num)

omit [NormedSpace ℝ E] in
/-- Zero extension preserves the literal L² time energy. -/
theorem zeroExtension_norm_sq_integral (T : ℝ) (u : TimeLp T E) :
    (∫ t, ‖zeroExtension T u t‖^2) = ‖u‖^2 := by
  calc
    (∫ t, ‖zeroExtension T u t‖^2) = ∫ t in Icc (0 : ℝ) T, ‖u t‖^2 := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Icc (0 : ℝ) T <;> simp [zeroExtension, ht]
    _ = ‖u‖^2 := (norm_sq_eq_integral T u).symm

/-- The sharp terminal trace bound at every time, with the global derivative energy. -/
theorem realPrimitive_norm_sq_le (T : ℝ) (u : TimeLp T E) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖realPrimitive T u t‖^2 ≤ (T-t)*‖u‖^2 := by
  have hlocal := norm_integral_sq_le_length_mul (zeroExtension T u) ht.2
    (zeroExtension_integrable T u).intervalIntegrable
    (zeroExtension_norm_sq_integrable T u).intervalIntegrable
  have hmono : (∫ s in t..T, ‖zeroExtension T u s‖^2) ≤ ‖u‖^2 := by
    rw [intervalIntegral.integral_of_le ht.2]
    exact (setIntegral_le_integral (zeroExtension_norm_sq_integrable T u)
      (Filter.Eventually.of_forall (fun s => sq_nonneg ‖zeroExtension T u s‖))).trans_eq
      (zeroExtension_norm_sq_integral T u)
  rw [realPrimitive, intervalIntegral.integral_symm, norm_neg]
  exact hlocal.trans (mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr ht.2))

/-- The pointwise square-root form of the sharp terminal trace estimate. -/
theorem realPrimitive_norm_le (T : ℝ) (u : TimeLp T E) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖realPrimitive T u t‖ ≤ Real.sqrt (T-t)*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht.2)]
  exact realPrimitive_norm_sq_le T u t ht

/-- The constructed representative is absolutely continuous, also for vector-valued inputs. -/
theorem realPrimitive_absolutelyContinuous (T : ℝ) (u : TimeLp T E) :
    AbsolutelyContinuousOnInterval (realPrimitive T u) 0 T := by
  let g : ℝ → ℝ := fun t => ∫ r in T..t, ‖zeroExtension T u r‖
  have hg : AbsolutelyContinuousOnInterval g 0 T :=
    (zeroExtension_integrable T
        u).norm.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      right_mem_uIcc
  have hd (s t : ℝ) : dist (realPrimitive T u s) (realPrimitive T u t) ≤ dist (g s) (g t) := by
    calc
      dist (realPrimitive T u s) (realPrimitive T u t) =
          ‖∫ r in t..s, zeroExtension T u r‖ := by rw [dist_eq_norm, realPrimitive_increment]
      _ ≤ |∫ r in t..s, ‖zeroExtension T u r‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      _ = dist (g s) (g t) := by
        rw [Real.dist_eq]
        congr 1
        exact (intervalIntegral.integral_interval_sub_left
          (zeroExtension_integrable T u).norm.intervalIntegrable
          (zeroExtension_integrable T u).norm.intervalIntegrable).symm
  exact squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun _ => Finset.sum_le_sum (fun _ _ => hd _ _)) hg

omit [NormedSpace ℝ E] in
/-- The zero extension respects addition as an actual Lebesgue almost-everywhere identity. -/
theorem zeroExtension_add_ae (T : ℝ) (u v : TimeLp T E) :
    zeroExtension T (u+v) =ᵐ[volume] fun t => zeroExtension T u t+zeroExtension T v t := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).mp (Lp.coeFn_add u v)
  filter_upwards [h] with t ht
  by_cases hm : t ∈ Icc (0 : ℝ) T
  · simpa [zeroExtension, hm] using ht
  · simp [zeroExtension, hm]

/-- The zero extension respects real scalar multiplication almost everywhere. -/
theorem zeroExtension_smul_ae (T : ℝ) (a : ℝ) (u : TimeLp T E) :
    zeroExtension T (a • u) =ᵐ[volume] fun t => a • zeroExtension T u t := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).mp (Lp.coeFn_smul a u)
  filter_upwards [h] with t ht
  by_cases hm : t ∈ Icc (0 : ℝ) T
  · simpa [zeroExtension, hm] using ht
  · simp [zeroExtension, hm]

/-- The primitive path respects addition of genuine L² equivalence classes. -/
theorem primitivePath_add (T : ℝ) (u v : TimeLp T E) :
    primitivePath T (u+v) = primitivePath T u+primitivePath T v := by
  ext t
  change (∫ r in T..t.val, zeroExtension T (u+v) r) =
    (∫ r in T..t.val, zeroExtension T u r)+(∫ r in T..t.val, zeroExtension T v r)
  rw [← intervalIntegral.integral_add (zeroExtension_integrable T u).intervalIntegrable
    (zeroExtension_integrable T v).intervalIntegrable]
  exact intervalIntegral.integral_congr_ae ((zeroExtension_add_ae T u v).mono (fun _ h _ => h))

/-- The primitive path respects real scalar multiplication. -/
theorem primitivePath_smul (T : ℝ) (a : ℝ) (u : TimeLp T E) :
    primitivePath T (a • u) = a • primitivePath T u := by
  ext t
  change (∫ r in T..t.val, zeroExtension T (a • u) r) = a • (∫ r in T..t.val, zeroExtension T u r)
  rw [← intervalIntegral.integral_smul]
  exact intervalIntegral.integral_congr_ae ((zeroExtension_smul_ae T a u).mono (fun _ h _ => h))

/-- The continuous-path norm is bounded by the sharp terminal trace constant. -/
theorem primitivePath_norm_le (T : ℝ) (_hT : 0 ≤ T) (u : TimeLp T E) :
    ‖primitivePath T u‖ ≤ Real.sqrt T*‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
  intro t
  exact (realPrimitive_norm_le T u t t.property).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (sub_le_self T t.property.1)) (norm_nonneg _))

/-- Bounded terminal integration from actual Bochner L² fields to continuous paths. -/
def terminalPrimitive (T : ℝ) (hT : 0 ≤ T) : TimeLp T E →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  ({ toFun := primitivePath T
     map_add' := primitivePath_add T
     map_smul' := fun a u => by simpa only [RingHom.id_apply] using primitivePath_smul T a u } :
      TimeLp T E →ₗ[ℝ] C(Icc (0 : ℝ) T, E)).mkContinuous (Real.sqrt T) (primitivePath_norm_le T hT)

/-- Evaluation is the actual integral representative. -/
@[simp] theorem terminalPrimitive_apply (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E)
    (t : Icc (0 : ℝ) T) : terminalPrimitive T hT u t = realPrimitive T u t := rfl

/-- The bounded primitive has exactly zero terminal trace. -/
theorem terminalPrimitive_terminal (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    terminalPrimitive T hT u ⟨T, hT, le_rfl⟩ = 0 := realPrimitive_terminal T u

/-- The sharp pointwise squared trace estimate for the bounded primitive. -/
theorem terminalPrimitive_apply_norm_sq_le (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E)
    (t : Icc (0 : ℝ) T) : ‖terminalPrimitive T hT u t‖^2 ≤ (T-t.val)*‖u‖^2 :=
  realPrimitive_norm_sq_le T u t t.property

/-- Evaluation at any interval point is a continuous linear map of the derivative. -/
def evaluation (T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) : TimeLp T E →L[ℝ] E :=
  (ContinuousMap.evalCLM ℝ t).comp (terminalPrimitive T hT)

/-- The initial trace, with its zero-terminal normalization. -/
def initialTrace (T : ℝ) (hT : 0 ≤ T) : TimeLp T E →L[ℝ] E :=
  evaluation T hT ⟨0, le_rfl, hT⟩

/-- The bounded primitive regarded as an actual Bochner L² time field. -/
def primitiveTimeLp (T : ℝ) (hT : 0 ≤ T) : TimeLp T E →L[ℝ] TimeLp T E :=
  (pathLpOperator T hT).comp (terminalPrimitive T hT)

/-- The Bochner primitive is represented by the same continuous real-time function. -/
theorem primitiveTimeLp_ae (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    (primitiveTimeLp T hT u : ℝ → E) =ᵐ[timeMeasure T] realPrimitive T u := by
  change (pathLp T hT (terminalPrimitive T hT u) : ℝ → E) =ᵐ[timeMeasure T] realPrimitive T u
  filter_upwards [pathLp_ae T hT (terminalPrimitive T hT u),
    ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht]
  change realPrimitive T u (projIcc 0 T hT t) = realPrimitive T u t
  rw [projIcc_of_mem hT hmem]

/-- The primitive's increments within the interval are literal integrals of its L² derivative. -/
theorem terminalPrimitive_increment (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E)
    (s t : Icc (0 : ℝ) T) :
    terminalPrimitive T hT u t-terminalPrimitive T hT u s = ∫ r in s.val..t.val, u r := by
  rw [terminalPrimitive_apply, terminalPrimitive_apply, realPrimitive_increment]
  apply intervalIntegral.integral_congr
  intro r hr
  have hm : r ∈ Icc (0 : ℝ) T :=
    (uIcc_subset_Icc s.property t.property) hr
  exact Set.indicator_of_mem hm _

/-- The explicit initial trace is the negative total integral of the derivative. -/
theorem initialTrace_eq_integral (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    initialTrace T hT u = -(∫ t in 0..T, u t) :=
  realPrimitive_eq_neg_integral T u 0 ⟨le_rfl, hT⟩

/-- The initial trace has the exact squared energy estimate from the source. -/
theorem initialTrace_norm_sq_le (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    ‖initialTrace T hT u‖^2 ≤ T*‖u‖^2 := by
  change ‖terminalPrimitive T hT u ⟨0, le_rfl, hT⟩‖^2 ≤ T*‖u‖^2
  simpa only [sub_zero] using terminalPrimitive_apply_norm_sq_le T hT u ⟨0, le_rfl, hT⟩

/-- The operator norm of terminal integration is bounded by the square root of the interval length.
-/
theorem terminalPrimitive_norm_le (T : ℝ) (hT : 0 ≤ T) :
    ‖terminalPrimitive (E := E) T hT‖ ≤ Real.sqrt T :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (primitivePath_norm_le T hT)

/-- Evaluation retains the sharper bound corresponding to the remaining interval length. -/
theorem evaluation_norm_le (T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) :
    ‖evaluation (E := E) T hT t‖ ≤ Real.sqrt (T-t.val) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  exact realPrimitive_norm_le T u t t.property

/-- The initial trace is a bounded map with the exact source trace constant. -/
theorem initialTrace_norm_le (T : ℝ) (hT : 0 ≤ T) :
    ‖initialTrace (E := E) T hT‖ ≤ Real.sqrt T := by
  change ‖evaluation (E := E) T hT ⟨0, le_rfl, hT⟩‖ ≤ Real.sqrt T
  simpa only [sub_zero] using evaluation_norm_le (E := E) T hT ⟨0, le_rfl, hT⟩

/-- The integral version of the terminal Poincaré estimate, for actual L² derivative data. -/
theorem realPrimitive_poincare (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    (∫ t in 0..T, ‖realPrimitive T u t‖^2) ≤ T^2/2*‖u‖^2 := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((realPrimitive_continuous T u).norm.pow 2).intervalIntegrable 0 T)
    (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable (a := 0) (b :=
        T))
    (fun t ht => realPrimitive_norm_sq_le T u t ht)
  have he : (∫ t in 0..T, (T-t)*‖u‖^2) = T^2/2*‖u‖^2 := by
    have hic : IntervalIntegrable (fun _ : ℝ => T) volume 0 T := intervalIntegrable_const
    have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 T := continuous_id.intervalIntegrable 0
        T
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub hic hid,
      intervalIntegral.integral_const, integral_id]
    simp only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_eq_mul]
    ring
  exact hi.trans_eq he

/-- The sharp source Poincaré constant for the genuine bounded Bochner primitive. -/
theorem primitiveTimeLp_norm_sq_le (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    ‖primitiveTimeLp T hT u‖^2 ≤ T^2/2*‖u‖^2 := by
  rw [norm_sq_eq_integral]
  have he : (∫ t, ‖(primitiveTimeLp T hT u : ℝ → E) t‖^2 ∂timeMeasure T) =
      ∫ t in 0..T, ‖realPrimitive T u t‖^2 := by
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae ((primitiveTimeLp_ae T hT u).mono
      (fun _ h => congrArg (fun v : E => ‖v‖^2) h))
  rw [he]
  exact realPrimitive_poincare T hT u

/-- The corresponding operator norm bound, suitable for composing variational forms. -/
theorem primitiveTimeLp_norm_le (T : ℝ) (hT : 0 ≤ T) :
    ‖primitiveTimeLp (E := E) T hT‖ ≤ Real.sqrt (T^2/2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact primitiveTimeLp_norm_sq_le T hT u

/-- Distinct derivative classes give distinct terminal-zero paths.
Thus Bochner L², equipped with the derivative norm, is a faithful Hilbert model
of these terminal H¹ paths when the target is a Hilbert space. -/
theorem terminalPrimitive_injective [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T) :
    Function.Injective (terminalPrimitive (E := E) T hT) := by
  intro u v huv
  apply Lp.ext
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [realPrimitive_hasDerivAt_ae T u, realPrimitive_hasDerivAt_ae T v, hmem]
    with t hu hv ht
  have he : realPrimitive T u =ᶠ[𝓝 t] realPrimitive T v := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact congrArg (fun f : C(Icc (0 : ℝ) T, E) => f ⟨s, hs.1.le, hs.2.le⟩) huv
  exact hu.unique (hv.congr_of_eventuallyEq he)

/-- Every absolutely continuous terminal-zero path with the prescribed L²
derivative is the constructed primitive.  This identifies arbitrary genuine H¹
test paths with the derivative-coordinate model used by the variational form. -/
theorem eq_realPrimitive_of_ac_hasDerivAt_ae [CompleteSpace E]
    (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) (η : ℝ → E)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (u t) t)
    (hterminal : η T = 0) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    η t = realPrimitive T u t := by
  have hdiff := hη.sub (realPrimitive_absolutelyContinuous T u)
  have hz : ∀ᵐ s ∂timeMeasure T, HasDerivAt (η-realPrimitive T u) 0 s := by
    filter_upwards [hder, realPrimitive_hasDerivAt_ae T u] with s hs hj
    simpa only [sub_self] using hs.sub hj
  have hz' : ∀ᵐ s, s ∈ uIcc (0 : ℝ) T → HasDerivAt (η-realPrimitive T u) 0 s := by
    rw [uIcc_of_le hT]
    exact (ae_restrict_iff' measurableSet_Icc).mp hz
  obtain ⟨c, hc⟩ := hdiff.const_of_ae_hasDerivAt_zero hz'
  have hc0 : c = 0 := by
    have he := hc T right_mem_uIcc
    simpa only [Pi.sub_apply, hterminal, realPrimitive_terminal, sub_self] using he.symm
  have he := hc t (by simpa only [uIcc_of_le hT] using ht)
  rw [hc0] at he
  exact sub_eq_zero.mp he

end EulerTerminalTimePrimitive
