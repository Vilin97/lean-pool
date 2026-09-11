/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual spatial translations of the fixed mean time space

Translation preserves ordinary solenoidal L² and its Bochner time space. The
action is isometric and strongly continuous and commutes with the actual
terminal primitive and initial trace.
-/

section

/-!
# Strong continuity of isometric spatial actions on time L²

This uses dominated convergence with the actual square-integrable time field.
It does not assume operator-norm continuity of spatial translations.
-/

@[expose] public section

noncomputable section

namespace EulerTimeLpBoundedMap

open MeasureTheory Set Filter EulerTimeLp
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A pointwise formula for the square distance between two genuine lifted fields. -/
theorem timeLift_norm_sub_sq (T : ℝ) (A B : E →L[ℝ] E) (u : TimeLp T E) :
    ‖timeLift T A u-timeLift T B u‖^2 =
      ∫ t, ‖A (u t)-B (u t)‖^2 ∂timeMeasure T := by
  refine (norm_sq_eq_integral T (timeLift T A u-timeLift T B u)).trans ?_
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (timeLift T A u) (timeLift T B u),
    timeLift_ae T A u, timeLift_ae T B u] with t hs ha hb
  simp only [Pi.sub_apply, ha, hb] at hs
  exact congrArg (fun v : E => ‖v‖^2) hs

/-- A strongly continuous family of spatial isometries remains strongly
continuous on the genuine Bochner time space. -/
theorem timeLift_strongly_continuous {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (T : ℝ) (A : X → E →L[ℝ] E)
    (hA : ∀ x v, ‖A x v‖ = ‖v‖)
    (hc : ∀ v, Continuous (fun x => A x v)) (u : TimeLp T E) :
    Continuous (fun x => timeLift T (A x) u) := by
  apply continuous_iff_continuousAt.2
  intro x₀
  let g : X → ℝ → ℝ := fun x t => ‖A x (u t)-A x₀ (u t)‖^2
  have hm (x : X) : AEStronglyMeasurable (g x) (timeMeasure T) := by
    exact (((A x).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).sub
      ((A x₀).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))).norm.pow 2
  have hb (x : X) (t : ℝ) : ‖g x t‖ ≤ 4*‖u t‖^2 := by
    have hn : ‖A x (u t)-A x₀ (u t)‖ ≤ 2*‖u t‖ := by
      calc
        _ ≤ ‖A x (u t)‖+‖A x₀ (u t)‖ := norm_sub_le _ _
        _ = 2*‖u t‖ := by rw [hA, hA]; ring
    calc
      ‖g x t‖ = ‖A x (u t)-A x₀ (u t)‖^2 := Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ (2*‖u t‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = 4*‖u t‖^2 := by ring
  have hi : Integrable (fun t => 4*‖u t‖^2) (timeMeasure T) :=
    ((Lp.memLp u).integrable_norm_pow (by norm_num)).const_mul 4
  have hl (t : ℝ) : Tendsto (fun x => g x t) (𝓝 x₀) (𝓝 (0 : ℝ)) := by
    have h := (((hc (u t)).tendsto x₀).sub_const (A x₀ (u t))).norm.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hint : Tendsto (fun x => ∫ t, g x t ∂timeMeasure T) (𝓝 x₀) (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (fun t => 4*‖u t‖^2)
        (Eventually.of_forall hm) (Eventually.of_forall (fun x => Eventually.of_forall (hb x))) hi
        (Eventually.of_forall hl))
  have hs : Tendsto (fun x => ‖timeLift T (A x) u-timeLift T (A x₀) u‖^2)
      (𝓝 x₀) (𝓝 (0 : ℝ)) := by
    exact hint.congr' (Eventually.of_forall (fun x => (timeLift_norm_sub_sq T (A x) (A x₀) u).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

end EulerTimeLpBoundedMap

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanTimeTranslation

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerTimeLp EulerTerminalTimePrimitive EulerTimeLpBoundedMap

/-- Spatial translation restricted to the actual ordinary solenoidal space. -/
def solenoidalTranslation (a : Space) : solenoidalSpace →ₗᵢ[ℝ] solenoidalSpace where
  toLinearMap := ((translation a).toLinearMap.comp solenoidalSpace.subtype).codRestrict
    solenoidalSpace (fun u => translation_solenoidal_mem a u.property)
  norm_map' := fun u => (translation a).norm_map (u : L2)

@[simp] theorem solenoidalTranslation_coe (a : Space) (u : solenoidalSpace) :
    (solenoidalTranslation a u : L2) = translation a (u : L2) := rfl

theorem solenoidalTranslation_add (a b : Space) (u : solenoidalSpace) :
    solenoidalTranslation a (solenoidalTranslation b u) = solenoidalTranslation (a+b) u :=
  Subtype.ext (translation_add a b (u : L2))

@[simp] theorem solenoidalTranslation_zero (u : solenoidalSpace) :
    solenoidalTranslation 0 u = u := Subtype.ext (translation_zero (u : L2))

/-- Strong continuity is proved for every ordinary L² equivalence class. -/
theorem translation_continuous (u : L2) : Continuous (fun a : Space => translation a u) := by
  let g : Space → C(Space, Space) := fun a => ⟨fun x => x+a, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_add_right (volume : Measure Space) a) (by norm_num)

/-- The same strong continuity holds on the closed solenoidal subspace. -/
theorem solenoidalTranslation_continuous (u : solenoidalSpace) :
    Continuous (fun a : Space => solenoidalTranslation a u) :=
  (translation_continuous (u : L2)).subtype_mk (fun a => translation_solenoidal_mem a u.property)

/-- Actual spatial translation at every Bochner time slice. -/
def timeTranslation (T : ℝ) (a : Space) : TimeLp T L2 →ₗᵢ[ℝ] TimeLp T L2 :=
  timeLiftIsometry T (translation a)

/-- Actual spatial translation on the fixed solenoidal time Hilbert space. -/
def timeSolenoidalTranslation (T : ℝ) (a : Space) :
    TimeLp T solenoidalSpace →ₗᵢ[ℝ] TimeLp T solenoidalSpace :=
  timeLiftIsometry T (solenoidalTranslation a)

theorem timeTranslation_ae (T : ℝ) (a : Space) (u : TimeLp T L2) :
    timeTranslation T a u =ᵐ[timeMeasure T] fun t => translation a (u t) :=
  timeLift_ae T (translation a).toContinuousLinearMap u

theorem timeSolenoidalTranslation_ae (T : ℝ) (a : Space) (u : TimeLp T solenoidalSpace) :
    timeSolenoidalTranslation T a u =ᵐ[timeMeasure T] fun t => solenoidalTranslation a (u t) :=
  timeLift_ae T (solenoidalTranslation a).toContinuousLinearMap u

theorem timeTranslation_add (T : ℝ) (a b : Space) (u : TimeLp T L2) :
    timeTranslation T a (timeTranslation T b u) = timeTranslation T (a+b) u := by
  apply Lp.ext
  filter_upwards [timeTranslation_ae T a (timeTranslation T b u), timeTranslation_ae T b u,
    timeTranslation_ae T (a+b) u] with t ha hb hab
  exact (ha.trans (congrArg (translation a) hb)).trans ((translation_add a b (u t)).trans hab.symm)

@[simp] theorem timeTranslation_zero (T : ℝ) (u : TimeLp T L2) : timeTranslation T 0 u = u := by
  apply Lp.ext
  filter_upwards [timeTranslation_ae T 0 u] with t ht
  exact ht.trans (translation_zero (u t))

theorem timeSolenoidalTranslation_add (T : ℝ) (a b : Space) (u : TimeLp T solenoidalSpace) :
    timeSolenoidalTranslation T a (timeSolenoidalTranslation T b u) =
      timeSolenoidalTranslation T (a+b) u := by
  apply Lp.ext
  filter_upwards [timeSolenoidalTranslation_ae T a (timeSolenoidalTranslation T b u),
    timeSolenoidalTranslation_ae T b u, timeSolenoidalTranslation_ae T (a+b) u] with t ha hb hab
  exact (ha.trans (congrArg (solenoidalTranslation a) hb)).trans
    ((solenoidalTranslation_add a b (u t)).trans hab.symm)

@[simp] theorem timeSolenoidalTranslation_zero (T : ℝ) (u : TimeLp T solenoidalSpace) :
    timeSolenoidalTranslation T 0 u = u := by
  apply Lp.ext
  filter_upwards [timeSolenoidalTranslation_ae T 0 u] with t ht
  exact ht.trans (solenoidalTranslation_zero (u t))

/-- The actual spatial action is continuous in translation for every time-L² field. -/
theorem timeTranslation_continuous (T : ℝ) (u : TimeLp T L2) :
    Continuous (fun a : Space => timeTranslation T a u) :=
  timeLift_strongly_continuous T (fun a => (translation a).toContinuousLinearMap)
    (fun a => (translation a).norm_map) translation_continuous u

/-- Strong continuity on the fixed mean derivative space. -/
theorem timeSolenoidalTranslation_continuous (T : ℝ) (u : TimeLp T solenoidalSpace) :
    Continuous (fun a : Space => timeSolenoidalTranslation T a u) :=
  timeLift_strongly_continuous T (fun a => (solenoidalTranslation a).toContinuousLinearMap)
    (fun a => (solenoidalTranslation a).norm_map) solenoidalTranslation_continuous u

theorem timeTranslation_realPrimitive (T : ℝ) (a : Space) (u : TimeLp T L2) (t : ℝ) :
    realPrimitive T (timeTranslation T a u) t = translation a (realPrimitive T u t) :=
  realPrimitive_timeLift T (translation a).toContinuousLinearMap u t

theorem timeSolenoidalTranslation_realPrimitive (T : ℝ) (a : Space)
    (u : TimeLp T solenoidalSpace) (t : ℝ) :
    realPrimitive T (timeSolenoidalTranslation T a u) t =
      solenoidalTranslation a (realPrimitive T u t) :=
  realPrimitive_timeLift T (solenoidalTranslation a).toContinuousLinearMap u t

theorem timeTranslation_initialTrace (T : ℝ) (hT : 0 ≤ T) (a : Space) (u : TimeLp T L2) :
    initialTrace T hT (timeTranslation T a u) = translation a (initialTrace T hT u) :=
  initialTrace_timeLift T hT (translation a).toContinuousLinearMap u

theorem timeSolenoidalTranslation_initialTrace (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (u : TimeLp T solenoidalSpace) :
    initialTrace T hT (timeSolenoidalTranslation T a u) =
      solenoidalTranslation a (initialTrace T hT u) :=
  initialTrace_timeLift T hT (solenoidalTranslation a).toContinuousLinearMap u

theorem timeTranslation_primitiveTimeLp (T : ℝ) (hT : 0 ≤ T) (a : Space) (u : TimeLp T L2) :
    primitiveTimeLp T hT (timeTranslation T a u) = timeTranslation T a (primitiveTimeLp T hT u) :=
  primitiveTimeLp_timeLift T hT (translation a).toContinuousLinearMap u

theorem timeSolenoidalTranslation_primitiveTimeLp (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (u : TimeLp T solenoidalSpace) :
    primitiveTimeLp T hT (timeSolenoidalTranslation T a u) =
      timeSolenoidalTranslation T a (primitiveTimeLp T hT u) :=
  primitiveTimeLp_timeLift T hT (solenoidalTranslation a).toContinuousLinearMap u

end EulerMeanTimeTranslation
