/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldRestriction
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-! Actual backward particle flows of smooth finite-energy truncations.
The maps are clamped outside the chosen interval, preserving volume at every
real parameter. Reversing from the other endpoint recovers the original
coefficient and supplies the forward paths used in local trapping arguments. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology BoundedContinuousFunction

namespace Euler.ComparatorBridge.TruncatedBackwardFlow

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  (A : SmoothTimeField (Icc (0 : ℝ) 1) E E)
  (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)

/-- Time reversal into the original unit interval. -/
def reverseTime : C(Icc (0 : ℝ) T, Icc (0 : ℝ) 1) where
  toFun s := ⟨T - s, sub_nonneg.mpr s.property.2,
    (sub_le_self T s.property.1).trans hT1⟩
  continuous_toFun := by fun_prop

/-- Minus the original velocity at reversed time. -/
def reverseField : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  (A.compTime (reverseTime T hT1)).map (-ContinuousLinearMap.id ℝ E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem reverseField_apply (s : Icc (0 : ℝ) T) (x : E) :
    (reverseField A T hT1).field s x = -A.field (reverseTime T hT1 s) x := by
  simp [reverseField]

/-- The existing global Picard construction for the reversed field. -/
def flowData : EulerBoundedLipschitzFlow.Data E :=
  EulerSmoothBanachFlow.flowData T hT (reverseField A T hT1)

/-- Backward flow homeomorphisms, clamped outside the chosen interval. -/
def homeomorph (s : ℝ) : E ≃ₜ E :=
  (flowData A T hT hT1).flowHomeomorph 0 (projIcc 0 T hT s)

/-- The globally defined, endpoint-extended backward coefficient. -/
def velocity (s : ℝ) (x : E) : E := (flowData A T hT hT1).velocity s x

omit [FiniteDimensional ℝ E] in
@[simp] theorem velocity_eq (s : ℝ) (x : E) :
    velocity A T hT hT1 s x =
      -A.field (reverseTime T hT1 (projIcc 0 T hT s)) x := by
  change (reverseField A T hT1).field (projIcc 0 T hT s) x = _
  exact reverseField_apply A T hT1 _ x

omit [FiniteDimensional ℝ E] in
/-- On the interval, the velocity is the original field at reversed time. -/
theorem velocity_eq_realField (s : ℝ) (hs : s ∈ Icc 0 T) (x : E) :
    velocity A T hT hT1 s x = -A.realField 1 zero_le_one (T - s) x := by
  rw [velocity_eq]
  simp only [SmoothTimeField.realField, EulerVolterraConvolution.extendPath,
    projIcc_of_mem hT hs,
    projIcc_of_mem zero_le_one (show T-s ∈ Icc (0 : ℝ) 1 from
      ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩)]
  rfl

@[simp] theorem homeomorph_apply (s : ℝ) (x : E) :
    homeomorph A T hT hT1 s x =
      (flowData A T hT hT1).forward (projIcc 0 T hT s) x := rfl

@[simp] theorem homeomorph_zero (x : E) :
    homeomorph A T hT hT1 0 x = x := by
  rw [homeomorph_apply]
  simp only [projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)]
  exact (flowData A T hT hT1).forward_zero x

theorem homeomorph_joint_continuous :
    Continuous (fun sx : ℝ × E => homeomorph A T hT hT1 sx.1 sx.2) := by
  exact (flowData A T hT hT1).forward_joint_continuous.comp
    (((continuous_subtype_val.comp (continuous_projIcc (a := 0) (b := T) (h := hT))).comp
      continuous_fst).prodMk
      continuous_snd)

omit [FiniteDimensional ℝ E] in
theorem velocity_joint_continuous :
    Continuous (Function.uncurry (velocity A T hT hT1)) :=
  (flowData A T hT hT1).continuous

theorem curve_continuous (x : E) :
    Continuous (fun s => homeomorph A T hT hT1 s x) :=
  (homeomorph_joint_continuous A T hT hT1).comp
    (continuous_id.prodMk continuous_const)

theorem speed_continuous (x : E) :
    Continuous (fun s => velocity A T hT hT1 s (homeomorph A T hT hT1 s x)) := by
  convert (velocity_joint_continuous A T hT hT1).comp
    (continuous_id.prodMk (curve_continuous A T hT hT1 x)) using 1
  rfl

theorem curve_hasDerivAt (x : E) (s : ℝ) (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => homeomorph A T hT hT1 r x)
      (velocity A T hT hT1 s (homeomorph A T hT hT1 s x)) s := by
  have he : (fun r => homeomorph A T hT hT1 r x) =ᶠ[𝓝 s]
      (fun r => (flowData A T hT hT1).forward r x) := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
    simp only [homeomorph_apply, projIcc_of_mem hT hr]
  have hd := (flowData A T hT hT1).forward_hasDerivAt s x
  have hv : homeomorph A T hT hT1 s x = (flowData A T hT hT1).forward s x := by
    simp only [homeomorph_apply, projIcc_of_mem hT ⟨hs.1.le, hs.2.le⟩]
  rw [hv]
  exact hd.congr_of_eventuallyEq he

/-- A trajectory in the original time direction. -/
def endpointPath (a : E) (r : ℝ) : E :=
  (flowData A T hT hT1).flow T (T-r) a

@[simp] theorem endpointPath_zero (a : E) : endpointPath A T hT hT1 a 0 = a := by
  simp only [endpointPath, sub_zero, EulerBoundedLipschitzFlow.Data.flow_initial]

@[simp] theorem endpointPath_end (a : E) :
    endpointPath A T hT hT1 a T = (homeomorph A T hT hT1 T).symm a := by
  change (flowData A T hT hT1).flow T (T-T) a =
    (flowData A T hT hT1).flow (projIcc 0 T hT T) 0 a
  simp only [sub_self, projIcc_of_mem hT (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)]

theorem endpointPath_continuous (a : E) : Continuous (endpointPath A T hT hT1 a) :=
  ((flowData A T hT hT1).flow_continuous_time T a).comp
    (continuous_const.sub continuous_id)

theorem endpointPath_hasDerivAt (a : E) (r : ℝ) (hr : r ∈ Ioo 0 T) :
    HasDerivAt (endpointPath A T hT hT1 a)
      (A.realField 1 zero_le_one r (endpointPath A T hT hT1 a r)) r := by
  unfold endpointPath
  have hd := ((flowData A T hT hT1).flow_hasDerivAt T (T-r) a).scomp r
    ((hasDerivAt_const r T).sub (hasDerivAt_id r))
  have hv := velocity_eq_realField A T hT hT1 (T-r)
    (show T-r ∈ Icc 0 T from ⟨by linarith [hr.2], by linarith [hr.1]⟩)
    (endpointPath A T hT hT1 a r)
  simp only [sub_sub_cancel] at hv
  change (flowData A T hT hT1).velocity (T-r)
    ((flowData A T hT hT1).flow T (T-r) a) = _ at hv
  simpa only [Function.comp_def, zero_sub, neg_smul, one_smul, hv,
    neg_neg, endpointPath] using hd

/-- The same derivative with the original subtype-indexed coefficient. -/
theorem endpointPath_hasDerivAt_field (a : E) (r : ℝ) (hr : r ∈ Ioo 0 T) :
    HasDerivAt (endpointPath A T hT hT1 a)
      (A.field ⟨r, hr.1.le, hr.2.le.trans hT1⟩
        (endpointPath A T hT hT1 a r)) r := by
  simpa only [SmoothTimeField.realField, EulerVolterraConvolution.extendPath,
    projIcc_of_mem zero_le_one ⟨hr.1.le, hr.2.le.trans hT1⟩] using
      endpointPath_hasDerivAt A T hT hT1 a r hr

omit [FiniteDimensional ℝ E] in
theorem reverseField_divergence
    (hdiv : ∀ t x, LinearMap.trace ℝ E (fderiv ℝ (A.field t : E → E) x).toLinearMap = 0)
    (s : Icc (0 : ℝ) T) (x : E) :
    LinearMap.trace ℝ E
      (fderiv ℝ ((reverseField A T hT1).field s : E → E) x).toLinearMap = 0 := by
  have he : ((reverseField A T hT1).field s : E → E) =
      fun y => -A.field (reverseTime T hT1 s) y := by
    ext y
    exact reverseField_apply A T hT1 s y
  rw [he, fderiv_fun_neg]
  change LinearMap.trace ℝ E
    (-(fderiv ℝ (A.field (reverseTime T hT1 s) : E → E) x).toLinearMap) = 0
  rw [map_neg, hdiv, neg_zero]

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem homeomorph_measurePreserving
    (hdiv : ∀ t x, LinearMap.trace ℝ E (fderiv ℝ (A.field t : E → E) x).toLinearMap = 0)
    (s : ℝ) : MeasurePreserving (homeomorph A T hT hT1 s) μ μ := by
  exact EulerSmoothBanachFlow.forward_measurePreserving T hT (reverseField A T hT1)
    (reverseField_divergence A T hT1 hdiv) μ (projIcc 0 T hT s)

omit [FiniteDimensional ℝ E] [BorelSpace E] [Measure.IsAddHaarMeasure μ] in
theorem velocity_memLp (hmem : ∀ t, MemLp (A.field t : E → E) 2 μ) (s : ℝ) :
    MemLp (velocity A T hT hT1 s) 2 μ := by
  have he : velocity A T hT hT1 s =
      fun x => -A.field (reverseTime T hT1 (projIcc 0 T hT s)) x := by
    funext x
    exact velocity_eq A T hT hT1 s x
  rw [he]
  exact (hmem _).neg

omit [FiniteDimensional ℝ E] [BorelSpace E] [Measure.IsAddHaarMeasure μ] in
theorem velocity_energy (energy : ℝ)
    (henergy : ∀ t, (∫ x, ‖A.field t x‖ ^ 2 ∂μ) ≤ energy) (s : ℝ) :
    (∫ x, ‖velocity A T hT hT1 s x‖ ^ 2 ∂μ) ≤ energy := by
  simp only [velocity_eq, norm_neg]
  exact henergy _

omit [Measure.IsAddHaarMeasure μ] in
theorem action_joint_measurable :
    AEStronglyMeasurable
      (fun sx : ℝ × E => ‖velocity A T hT hT1 sx.1
        (homeomorph A T hT hT1 sx.1 sx.2)‖ ^ 2)
      ((volume.restrict (Icc 0 T)).prod μ) := by
  exact (((velocity_joint_continuous A T hT hT1).comp
    (continuous_fst.prodMk (homeomorph_joint_continuous A T hT hT1))).norm.pow
      2).aestronglyMeasurable

end Measure

end Euler.ComparatorBridge.TruncatedBackwardFlow
