/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TruncationFamily
import LeanPool.NavierStokesAndEuler.Euler.ScalarEulerVorticity
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import LeanPool.NavierStokesAndEuler.Euler.FlowEscapeBound
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldRestriction
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import LeanPool.NavierStokesAndEuler.Euler.SmoothBanachFlow
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Short-time compact vorticity from finite-energy truncations

The auxiliary characteristics are global flows of compact solenoidal
truncations. The construction does not require global trajectories of the
untruncated Comparator velocity.
-/

section

/-! Actual backward particle flows of smooth finite-energy truncations.
The maps are clamped outside the chosen interval, preserving volume at every
real parameter. Reversing from the other endpoint recovers the original
coefficient and supplies the forward paths used in local trapping arguments. -/

@[expose] public section

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

theorem homeomorph_zero (x : E) :
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

end
end

end

section

/-!
# No vorticity arriving from spatial infinity

The flow hypotheses below describe globally defined approximations to backward
characteristics. Their kinetic energy is uniformly bounded. On paths which
stay inside the approximation radius, nonzero endpoint vorticity must come
from the initial vorticity support. Initial support is trapped by the inverse
endpoint maps in one common ball. These hypotheses exclude all nonzero
vorticity outside that ball; no global pointwise velocity bound is needed.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Euler.ComparatorBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

private theorem positive_volume_set_of_nonzero_outside
    (w : ℝ³ → ℝ³) (hw : Continuous w) (B : ℝ) (x : ℝ³)
    (hxB : B < ‖x‖) (hxw : w x ≠ 0) :
    ∃ S : Set ℝ³, MeasurableSet S ∧ volume S ≠ ⊤ ∧
      0 < volume.real S ∧ ∃ K₀ : ℝ,
      ∀ y ∈ S, ‖y‖ ≤ K₀ ∧ B < ‖y‖ ∧ w y ≠ 0 := by
  have hU : IsOpen ({y : ℝ³ | B < ‖y‖} ∩ {y : ℝ³ | w y ≠ 0}) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_ne.preimage hw)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x ⟨hxB, hxw⟩
  refine ⟨Metric.ball x r, measurableSet_ball, measure_ball_ne_top,
    ?_, ‖x‖ + r, ?_⟩
  · exact ENNReal.toReal_pos
      (Metric.measure_ball_pos volume x hr).ne' measure_ball_ne_top
  · intro y hy
    exact ⟨norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hy).le, hsub hy⟩

/-- Approximate backward characteristics for a vorticity field at one time.
The parameter `R` is the spatial radius on which transport is valid. The
time parameter `s` runs backward from the endpoint (`s=0`) to the initial
time (`s=T`). -/
structure BackwardVorticityFlows
    (T energy supportRadius : ℝ) (K : Set ℝ³) (w₀ w : ℝ³ → ℝ³) where
  /-- Flow of `BackwardVorticityFlows`, of type `ℝ → ℝ → ℝ³ ≃ₜ ℝ³`. -/
  flow : ℝ → ℝ → ℝ³ ≃ₜ ℝ³
  /-- Velocity field of `BackwardVorticityFlows`, of type `ℝ → ℝ → ℝ³ → ℝ³`. -/
  velocity : ℝ → ℝ → ℝ³ → ℝ³
  time_nonneg : 0 ≤ T
  preserves_volume : ∀ R s, MeasurePreserving (flow R s) volume volume
  initial_map : ∀ R x, flow R 0 x = x
  joint_measurable : ∀ R, AEStronglyMeasurable
    (fun sx : ℝ × ℝ³ => ‖velocity R sx.1 (flow R sx.1 sx.2)‖ ^ 2)
    ((volume.restrict (Icc 0 T)).prod volume)
  velocity_memLp : ∀ R s, MemLp (velocity R s) 2 volume
  energy_bound : ∀ R s, (∫ x, ‖velocity R s x‖ ^ 2) ≤ energy
  curve_continuous : ∀ R x, ContinuousOn (fun s => flow R s x) (Icc 0 T)
  speed_continuous : ∀ R x,
    ContinuousOn (fun s => velocity R s (flow R s x)) (Icc 0 T)
  curve_derivative : ∀ R x s, s ∈ Ioo 0 T →
    HasDerivAt (fun r => flow R r x) (velocity R s (flow R s x)) s
  initial_support : Function.support w₀ ⊆ K
  transport_nonzero : ∀ R x,
    (∀ s ∈ Icc 0 T, ‖flow R s x‖ < R) → w x ≠ 0 → w₀ (flow R T x) ≠ 0
  forward_trap : ∀ R a, a ∈ K → ‖(flow R T).symm a‖ ≤ supportRadius

namespace BackwardVorticityFlows

variable {T energy supportRadius : ℝ} {K : Set ℝ³} {w₀ w : ℝ³ → ℝ³}
  (F : BackwardVorticityFlows T energy supportRadius K w₀ w)

include F

/-- A nonzero-vorticity endpoint outside the trapped support has to leave
every approximation ball when traced backward. -/
theorem escapes (R : ℝ) (x : ℝ³) (hx : supportRadius < ‖x‖) (hw : w x ≠ 0) :
    ∃ s ∈ Icc 0 T, R ≤ ‖F.flow R s x‖ := by
  by_contra hn
  have hstay : ∀ s ∈ Icc 0 T, ‖F.flow R s x‖ < R := by
    intro s hs
    exact lt_of_not_ge (fun hr => hn ⟨s, hs, hr⟩)
  have hstart : F.flow R T x ∈ K :=
    F.initial_support (F.transport_nonzero R x hstay hw)
  have htrap := F.forward_trap R (F.flow R T x) hstart
  have htrap' : ‖x‖ ≤ supportRadius := by
    simpa only [Homeomorph.symm_apply_apply] using htrap
  exact not_le_of_gt hx htrap'

/-- Every bounded measurable set of nonzero vorticity outside the support
ball has the quantitative escape bound. -/
theorem measure_nonzero_outside_le
    (S : Set ℝ³) (hS : MeasurableSet S) (hfinite : volume S ≠ ⊤)
    (K₀ R : ℝ) (hKR : K₀ < R)
    (hSbound : ∀ x ∈ S, ‖x‖ ≤ K₀)
    (hSoutside : ∀ x ∈ S, supportRadius < ‖x‖)
    (hSnonzero : ∀ x ∈ S, w x ≠ 0) :
    volume.real S ≤ energy * T ^ 2 / (R - K₀) ^ 2 := by
  apply flow_escape_measure_le volume T K₀ R energy F.time_nonneg hKR
    (fun s x => F.flow R s x) (F.velocity R)
    (F.preserves_volume R) (fun s => (F.flow R s).measurableEmbedding)
    (F.joint_measurable R) (F.velocity_memLp R) (F.energy_bound R)
    (F.curve_continuous R) (F.speed_continuous R) (F.curve_derivative R)
    S hS hfinite
  · intro x hx
    simpa only [F.initial_map] using hSbound x hx
  · intro x hx
    exact F.escapes R x (hSoutside x hx) (hSnonzero x hx)

/-- Sending the approximation radius to infinity rules out a positive
measure set of bounded nonzero-vorticity endpoints outside the trapped ball. -/
theorem measure_nonzero_outside_eq_zero
    (S : Set ℝ³) (hS : MeasurableSet S) (hfinite : volume S ≠ ⊤)
    (K₀ : ℝ) (hSbound : ∀ x ∈ S, ‖x‖ ≤ K₀)
    (hSoutside : ∀ x ∈ S, supportRadius < ‖x‖)
    (hSnonzero : ∀ x ∈ S, w x ≠ 0) : volume.real S = 0 := by
  have hlim : Tendsto (fun r : ℝ => energy * T ^ 2 / r ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have hz : volume.real S ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hh := F.measure_nonzero_outside_le S hS hfinite K₀ (K₀ + r)
      (by linarith) hSbound hSoutside hSnonzero
    simpa only [add_sub_cancel_left] using hh
  exact le_antisymm hz measureReal_nonneg

/-- Continuity removes the null exceptional set: vorticity vanishes
pointwise outside the common ball containing the transported initial support. -/
theorem zero_outside (hw : Continuous w) (x : ℝ³) (hx : supportRadius < ‖x‖) :
    w x = 0 := by
  by_contra hn
  obtain ⟨S, hS, hfinite, hpos, K₀, hprops⟩ :=
    positive_volume_set_of_nonzero_outside w hw supportRadius x hx hn
  have hz := F.measure_nonzero_outside_eq_zero S hS hfinite K₀
    (fun y hy => (hprops y hy).1) (fun y hy => (hprops y hy).2.1)
    (fun y hy => (hprops y hy).2.2)
  linarith

/-- The transported field is supported in one fixed compact ball. -/
theorem support_subset_closedBall (hw : Continuous w) :
    Function.support w ⊆ Metric.closedBall (0 : ℝ³) supportRadius := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_not_gt (fun hlt => hx (F.zero_outside hw x hlt))

theorem hasCompactSupport (hw : Continuous w) : HasCompactSupport w := by
  exact HasCompactSupport.intro (isCompact_closedBall (0 : ℝ³) supportRadius)
    (fun x hx => F.zero_outside hw x (by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))

end BackwardVorticityFlows
end Euler.ComparatorBridge

end
end

end

section

/-! Short-time confinement uses a velocity bound only inside the trapping ball. -/

@[expose] public section

noncomputable section

namespace EulerComparatorLocalFlow

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mean-value bound up to both endpoints, with derivatives required only in the interior. -/
theorem norm_sub_le_mul_of_hasDerivAt_Ioo (X X' : ℝ → E) {T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hX : ContinuousOn X (Icc 0 T))
    (hderiv : ∀ s ∈ Ioo 0 T, HasDerivAt X (X' s) s)
    (hbound : ∀ s ∈ Ioo 0 T, ‖X' s‖ ≤ M) :
    ‖X T - X 0‖ ≤ M * T := by
  have hlip : LipschitzOnWith ⟨M, hM⟩ X (Ioo 0 T) :=
    (convex_Ioo (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (hderiv s hs).hasDerivWithinAt) (fun s hs => hbound s hs)
  have hcl : closure (Ioo (0 : ℝ) T) = Icc 0 T := closure_Ioo hT.ne
  have hlipclosed : LipschitzOnWith ⟨M, hM⟩ X (Icc 0 T) := by
    rw [← hcl]
    exact LipschitzOnWith.closure (by simpa only [hcl] using hX) hlip
  have h := lipschitzOnWith_iff_dist_le_mul.mp hlipclosed
    T (right_mem_Icc.mpr hT.le) 0 (left_mem_Icc.mpr hT.le)
  change dist (X T) (X 0) ≤ M * dist T 0 at h
  simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hT] using h

/-- A trajectory cannot first leave the ball before the local speed budget is exhausted.
No bound on the velocity outside `‖x‖ ≤ B` is used. -/
theorem norm_lt_of_local_speed_bound (X : ℝ → E) (V : ℝ → E → E)
    {δ A B M : ℝ} (hM : 0 ≤ M) (hAB : A < B) (hsmall : δ * M < B - A)
    (hX : ContinuousOn X (Icc 0 δ))
    (hderiv : ∀ s ∈ Ioo 0 δ, HasDerivAt X (V s (X s)) s)
    (hinitial : ‖X 0‖ ≤ A)
    (hbound : ∀ s ∈ Icc 0 δ, ∀ x : E, ‖x‖ ≤ B → ‖V s x‖ ≤ M) :
    ∀ t ∈ Icc 0 δ, ‖X t‖ < B := by
  intro t ht
  by_contra hnot
  let S : Set ℝ := {s ∈ Icc 0 δ | B ≤ ‖X s‖}
  have hSc : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.isClosed_le continuousOn_const hX.norm) (fun _ h => h.1)
  have hSn : S.Nonempty := ⟨t, ht, le_of_not_gt hnot⟩
  obtain ⟨s, hs⟩ := hSc.exists_isLeast hSn
  have hsI : s ∈ Icc 0 δ := hs.1.1
  have hsbound : B ≤ ‖X s‖ := hs.1.2
  have hspos : 0 < s := by
    have hsne : s ≠ 0 := by
      intro h
      rw [h] at hsbound
      exact (not_le_of_gt hAB) (hsbound.trans hinitial)
    exact lt_of_le_of_ne hsI.1 hsne.symm
  have hinside : ∀ r ∈ Ioo 0 s, ‖X r‖ < B := by
    intro r hr
    by_contra hn
    have hrS : r ∈ S := ⟨⟨hr.1.le, hr.2.le.trans hsI.2⟩, le_of_not_gt hn⟩
    exact (not_le_of_gt hr.2) (hs.2 hrS)
  have hdisplacement : ‖X s - X 0‖ ≤ M * s :=
    norm_sub_le_mul_of_hasDerivAt_Ioo X (fun r => V r (X r)) hspos hM
      (hX.mono (fun _ hr => ⟨hr.1, hr.2.trans hsI.2⟩))
      (fun r hr => hderiv r ⟨hr.1, hr.2.trans_le hsI.2⟩)
      (fun r hr => hbound r ⟨hr.1.le, hr.2.le.trans hsI.2⟩ (X r) (hinside r hr).le)
  have hnorm : ‖X s‖ ≤ M * s + A := by
    calc
      ‖X s‖ = ‖(X s - X 0) + X 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖X s - X 0‖ + ‖X 0‖ := norm_add_le _ _
      _ ≤ M * s + A := add_le_add hdisplacement hinitial
  have hbudget : M * s ≤ M * δ := mul_le_mul_of_nonneg_left hsI.2 hM
  nlinarith

omit [NormedSpace ℝ E] in
/-- Compactness supplies a common speed bound and positive time budget on a fixed ball. -/
theorem exists_local_speed_budget [ProperSpace E] (u : ℝ → E → E) {A B : ℝ}
    (hAB : A < B)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : E) B)) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ δ * M < B - A ∧
      ∀ s ∈ Icc 0 δ, ∀ x : E, ‖x‖ ≤ B → ‖u s x‖ ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) B)).exists_bound_of_continuousOn hu
  let M : ℝ := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let δ : ℝ := min 1 ((B - A) / (2 * M))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos (sub_pos.mpr hAB) (by positivity))
  have hδone : δ ≤ 1 := min_le_left _ _
  have hsmall : δ * M < B - A := by
    have hb : δ * M ≤ (B - A) / 2 := by
      calc
        δ * M ≤ ((B - A) / (2 * M)) * M :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
        _ = (B - A) / 2 := by field_simp
    linarith
  refine ⟨δ, M, hδ, hδone, hM, hsmall, ?_⟩
  intro s hs x hx
  have hxball : x ∈ Metric.closedBall (0 : E) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hc := hC (s, x) ⟨⟨hs.1, hs.2.trans hδone⟩, hxball⟩
  have hCM : C ≤ M := (le_max_left C 0).trans (by dsimp [M]; linarith)
  exact hc.trans hCM

end EulerComparatorLocalFlow

end
end

end

section

/-! Nonzero vorticity cannot disappear on an existing reverse-time particle
trajectory of a Comparator solution. -/

@[expose] public section

noncomputable section

open Set EulerSmoothLimit EulerMeanCutoffCurl
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- A reverse-time particle path carrying nonzero vorticity at time `T`
reaches a point with nonzero initial vorticity. -/
theorem vorticity_ne_zero_along_reverse_trajectory
    (X : ℝ → Space) (T : ℝ) (hT : 0 ≤ T)
    (hX : ContinuousOn X (Icc 0 T))
    (hXd : ∀ s ∈ Ioo 0 T, HasDerivAt X (-v (X s) (T - s)) s)
    (hne : vectorCurl (v · T) (X 0) ≠ 0) :
    vectorCurl (v · 0) (X T) ≠ 0 := by
  intro hz
  have hY : ContinuousOn (fun r => X (T - r)) (Icc 0 T) :=
    hX.comp (continuousOn_const.sub continuousOn_id)
      (fun r hr => ⟨sub_nonneg.mpr hr.2, sub_le_self T hr.1⟩)
  have hYd : ∀ r ∈ Ioo 0 T,
      HasDerivAt (fun s => X (T - s)) (v (X (T - r)) r) r := by
    intro r hr
    have hs : T - r ∈ Ioo 0 T := ⟨sub_pos.mpr hr.2, sub_lt_self T hr.1⟩
    simpa only [sub_sub_cancel, neg_neg] using
      HasDerivAt.comp_const_sub T r (hXd (T - r) hs)
  have hi : vectorCurl (v · 0) (X (T - 0)) = 0 := by simpa using hz
  have he := h.vorticity_eq_zero_along_trajectory (fun r => X (T - r)) T
    hY hYd hi T ⟨hT, le_rfl⟩
  apply hne
  simpa only [sub_self] using he

/-- A path for a modified reverse-time velocity has the same nonzero
vorticity transport whenever that velocity agrees with Euler along the path. -/
theorem vorticity_ne_zero_along_reverse_trajectory_of_agrees
    (X : ℝ → Space) (w : ℝ → Space → Space) (T : ℝ) (hT : 0 ≤ T)
    (hX : ContinuousOn X (Icc 0 T))
    (hXd : ∀ s ∈ Ioo 0 T, HasDerivAt X (-w s (X s)) s)
    (hw : ∀ s ∈ Ioo 0 T, w s (X s) = v (X s) (T - s))
    (hne : vectorCurl (v · T) (X 0) ≠ 0) :
    vectorCurl (v · 0) (X T) ≠ 0 := by
  apply h.vorticity_ne_zero_along_reverse_trajectory X T hT hX _ hne
  intro s hs
  simpa only [hw s hs] using hXd s hs

end Euler.EulerExistenceAndSmoothnessR3

end
end

end

@[expose] public section

noncomputable section

open Set MeasureTheory EulerSmoothLimit EulerMeanCutoffCurl
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- One compact spacetime cylinder supplies a common local speed bound and
one positive trapping time for every truncation agreeing on that cylinder. -/
theorem exists_local_trapping_constants
    (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ A M δ : ℝ, 0 < A ∧ 0 < M ∧ 0 < δ ∧ δ ≤ 1 ∧ δ * M < 1 ∧
      (∀ x ∈ tsupport (vectorCurl u₀), ‖x‖ ≤ A) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ A + 1 → ‖v x t‖ ≤ M) := by
  obtain ⟨A, hA, hAbound⟩ := hc.isBounded.exists_pos_norm_le
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) (A + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hv : ContinuousOn (fun z : ℝ × Space => v z.2 z.1)
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) (A + 1)) :=
    h.velocity_joint_contDiffOn.continuousOn.mono (by
      intro z hz
      exact ⟨hz.1.1, mem_univ _⟩)
  obtain ⟨M, hM, hMb⟩ := (hcompact.image_of_continuousOn hv).isBounded.exists_pos_norm_le
  let δ : ℝ := min 1 (1 / (2 * M))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδM : δ * M < 1 := by
    have hm : δ * M ≤ (1 / (2 * M)) * M :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
    have he : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    rw [he] at hm
    linarith
  refine ⟨A, M, δ, hA, hM, hδ, min_le_left _ _, hδM, hAbound, ?_⟩
  intro t ht x hx
  apply hMb (v x t)
  refine ⟨(t, x), ⟨ht, ?_⟩, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx

omit h in
theorem truncation_realField_agrees
    (F : ComparatorBridge.FiniteEnergyTruncationFamily v)
    (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : r ∈ Icc 0 1)
    (x : Space) (hx : ‖x‖ < R) :
    (F.coefficient R).realField 1 zero_le_one r x = v x r := by
  change (F.coefficient R).field (projIcc 0 1 zero_le_one r) x = _
  rw [F.agrees R hR _ x hx]
  simp only [projIcc_of_mem zero_le_one hr]

/-- The approximation radius is enlarged to include the one fixed trapping
ball. This gives valid approximants even for nonpositive requested radii. -/
def locallyTrappedBackwardFlows
    (F : ComparatorBridge.FiniteEnergyTruncationFamily v)
    (A M δ T : ℝ) (hA : 0 < A) (hM : 0 < M)
    (hδ1 : δ ≤ 1) (hδM : δ * M < 1) (hT : T ∈ Icc 0 δ)
    (hAbound : ∀ x ∈ tsupport (vectorCurl u₀), ‖x‖ ≤ A)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ A + 1 → ‖v x t‖ ≤ M) :
    ComparatorBridge.BackwardVorticityFlows T F.energy (A + 1)
      (tsupport (vectorCurl u₀)) (vectorCurl u₀) (vectorCurl (v · T)) := by
  let ρ : ℝ → ℝ := fun R => max R (A + 2)
  have hρ (R : ℝ) : 0 < ρ R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT1 : T ≤ 1 := hT.2.trans hδ1
  let C (R : ℝ) := F.coefficient (ρ R)
  let X (R s : ℝ) := ComparatorBridge.TruncatedBackwardFlow.homeomorph (C R) T hT.1 hT1 s
  let V (R : ℝ) := ComparatorBridge.TruncatedBackwardFlow.velocity (C R) T hT.1 hT1
  refine {
    flow := X
    velocity := V
    time_nonneg := hT.1
    preserves_volume := ?_
    initial_map := ?_
    joint_measurable := ?_
    velocity_memLp := ?_
    energy_bound := ?_
    curve_continuous := ?_
    speed_continuous := ?_
    curve_derivative := ?_
    initial_support := subset_tsupport _
    transport_nonzero := ?_
    forward_trap := ?_ }
  · intro R s
    exact ComparatorBridge.TruncatedBackwardFlow.homeomorph_measurePreserving
      (C R) T hT.1 hT1 volume (F.divergence (ρ R) (hρ R)) s
  · intro R x
    exact ComparatorBridge.TruncatedBackwardFlow.homeomorph_zero (C R) T hT.1 hT1 x
  · intro R
    exact ComparatorBridge.TruncatedBackwardFlow.action_joint_measurable (C R) T hT.1 hT1 volume
  · intro R s
    exact ComparatorBridge.TruncatedBackwardFlow.velocity_memLp
      (C R) T hT.1 hT1 volume (F.memLp (ρ R) (hρ R)) s
  · intro R s
    exact ComparatorBridge.TruncatedBackwardFlow.velocity_energy
      (C R) T hT.1 hT1 volume F.energy (F.energy_bound (ρ R) (hρ R)) s
  · intro R x
    exact (ComparatorBridge.TruncatedBackwardFlow.curve_continuous (C R) T hT.1 hT1 x).continuousOn
  · intro R x
    exact (ComparatorBridge.TruncatedBackwardFlow.speed_continuous (C R) T hT.1 hT1 x).continuousOn
  · intro R x s hs
    exact ComparatorBridge.TruncatedBackwardFlow.curve_hasDerivAt (C R) T hT.1 hT1 x s hs
  · intro R x hstay hnz
    have he : (v · 0) = u₀ := funext h.initial_condition
    rw [← he]
    apply h.vorticity_ne_zero_along_reverse_trajectory
      (fun s => X R s x) T hT.1
      (ComparatorBridge.TruncatedBackwardFlow.curve_continuous (C R) T hT.1 hT1 x).continuousOn
    · intro s hs
      have hd := ComparatorBridge.TruncatedBackwardFlow.curve_hasDerivAt
        (C R) T hT.1 hT1 x s hs
      have hv : V R s (X R s x) = -v (X R s x) (T - s) := by
        change ComparatorBridge.TruncatedBackwardFlow.velocity (C R) T hT.1 hT1 s (X R s x) = _
        rw [ComparatorBridge.TruncatedBackwardFlow.velocity_eq_realField
          (C R) T hT.1 hT1 s ⟨hs.1.le, hs.2.le⟩]
        rw [truncation_realField_agrees F (ρ R) (hρ R) (T - s)
          ⟨sub_nonneg.mpr hs.2.le, by linarith [hs.1]⟩ (X R s x)
          ((hstay s ⟨hs.1.le, hs.2.le⟩).trans_le (le_max_left _ _))]
      exact hv ▸ hd
    · simpa only [X, ComparatorBridge.TruncatedBackwardFlow.homeomorph_zero] using hnz
  · intro R a ha
    let Z := ComparatorBridge.TruncatedBackwardFlow.endpointPath (C R) T hT.1 hT1 a
    have hsmall : T * M < (A + 1) - A := by
      have hm := mul_le_mul_of_nonneg_right hT.2 hM.le
      linarith
    have hz := EulerComparatorLocalFlow.norm_lt_of_local_speed_bound
      Z ((C R).realField 1 zero_le_one) hM.le (by linarith : A < A + 1) hsmall
      (ComparatorBridge.TruncatedBackwardFlow.endpointPath_continuous (C R) T hT.1 hT1
          a).continuousOn
      (ComparatorBridge.TruncatedBackwardFlow.endpointPath_hasDerivAt (C R) T hT.1 hT1 a)
      (by
          simpa only [Z, ComparatorBridge.TruncatedBackwardFlow.endpointPath_zero] using hAbound a
              ha)
      (by
        intro r hr x hx
        rw [truncation_realField_agrees F (ρ R) (hρ R) r ⟨hr.1, hr.2.trans hT1⟩ x
          (lt_of_le_of_lt hx (lt_of_lt_of_le (by linarith) (le_max_right _ _)))]
        exact hspeed r ⟨hr.1, hr.2.trans hT1⟩ x hx)
      T ⟨hT.1, le_rfl⟩
    simpa only [Z, X, ComparatorBridge.TruncatedBackwardFlow.endpointPath_end] using hz.le

/-- Finite-energy solenoidal truncations imply compact vorticity for a
uniform positive interval, using only the Comparator solution assumptions. -/
theorem local_compact_vorticity_of_truncationFamily
    (F : ComparatorBridge.FiniteEnergyTruncationFamily v)
    (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ δ B : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 δ,
      tsupport (vectorCurl (v · t)) ⊆ Metric.closedBall (0 : Space) B := by
  obtain ⟨A, M, δ, hA, hM, hδ, hδ1, hδM, hAbound, hspeed⟩ :=
    h.exists_local_trapping_constants hc
  refine ⟨δ, A + 1, hδ, ?_⟩
  intro t ht
  let G := h.locallyTrappedBackwardFlows F A M δ t hA hM hδ1 hδM ht hAbound hspeed
  exact closure_minimal (G.support_subset_closedBall
    (EulerMeanVectorIdentities.vectorCurl_smooth (v · t) (h.velocity_contDiff t ht.1)).continuous)
    Metric.isClosed_closedBall

/-- Compact initial vorticity stays in one compact ball for a positive time
for every Comparator solution. The auxiliary global trajectories are those
of the explicitly constructed finite-energy solenoidal truncations. -/
theorem local_compact_vorticity (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ δ B : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 δ,
      tsupport (vectorCurl (v · t)) ⊆ Metric.closedBall (0 : Space) B :=
  h.local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc

end Euler.EulerExistenceAndSmoothnessR3
