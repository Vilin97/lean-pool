/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureSpatialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Translation derivatives and actual weak derivatives on the lifted cylinder.
Smooth compact test fields are realized in L², and their translation orbits
are differentiated in the strong L² topology.
-/

@[expose] public section

noncomputable section

namespace EulerLiftedWeakDerivative

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerPressureSpatialRegularity
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference
shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace


variable (period : ℝ) [Fact (0 < period)]

section FieldCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The full derivative of a field in covering coordinates, evaluated at the center. -/
def fieldFDeriv (f : LiftDomain period → W) (x : LiftDomain period) : LiftTangent →L[ℝ] W :=
  fderiv ℝ (localFieldLift period f x) 0

omit [Fact (0 < period)] in
theorem localFieldLift_fieldFDeriv (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldFDeriv period f) x = fderiv ℝ (localFieldLift period f x) := by
  funext h
  exact fderiv_localFieldLift_shift period f x h

omit [Fact (0 < period)] in
theorem fieldFDeriv_smooth (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldFDeriv period f) x) := by
  rw [localFieldLift_fieldFDeriv]
  exact (hf x).fderiv_right (by simp)

omit [Fact (0 < period)] in
theorem fieldFDeriv_zero_outside (f : LiftDomain period → W) (x : LiftDomain period)
    (hx : x ∉ tsupport f) : fieldFDeriv period f x = 0 := by
  have hc : Continuous (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) :=
    (continuous_const.add continuous_fst).prodMk
      (continuous_const.add ((AddCircle.continuous_mk' period).comp continuous_snd))
  have ht : Filter.Tendsto (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : LiftTangent)
  have hz : localFieldLift period f x =ᶠ[𝓝 0] (fun _ : LiftTangent => (0 : W)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto ht
  change fderiv ℝ (localFieldLift period f x) 0 = 0
  rw [hz.fderiv_eq]
  simp

omit [Fact (0 < period)] in
theorem fieldFDeriv_compact (f : LiftDomain period → W) (hf : HasCompactSupport f) :
    HasCompactSupport (fieldFDeriv period f) :=
  HasCompactSupport.intro hf (fieldFDeriv_zero_outside period f)

omit [Fact (0 < period)] in
theorem fieldDerivative_compact (a : LiftTangent) (f : LiftDomain period → W)
    (hf : HasCompactSupport f) : HasCompactSupport (fieldDerivative period a f) := by
  apply (fieldFDeriv_compact period f hf).mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  change fieldFDeriv period f x a = 0
  rw [hx]
  rfl

theorem fieldDerivative_memLp (a : LiftTangent) (f : LiftDomain period → W)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    MemLp (fieldDerivative period a f) 2 (liftMeasure period) :=
  (smoothField_continuous period _ (fieldDerivative_smooth period a f
      hf)).memLp_of_hasCompactSupport
    (fieldDerivative_compact period a f hfc)

omit [Fact (0 < period)] in
theorem compact_smooth_second_derivative_bound (f : LiftDomain period → W)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∃ M : ℝ≥0, ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period f x)) y‖ ≤ M := by
  let F := fieldFDeriv period (fieldFDeriv period f)
  have hFc : HasCompactSupport F := fieldFDeriv_compact period _ (fieldFDeriv_compact period f hfc)
  have hFs : ∀ x, ContDiff ℝ ∞ (localFieldLift period F x) :=
    fieldFDeriv_smooth period _ (fieldFDeriv_smooth period f hf)
  have hFb := (hFc.isCompact_range (smoothField_continuous period F hFs)).isBounded
  obtain ⟨M, hM, hbound⟩ := hFb.exists_pos_norm_le
  refine ⟨⟨M, hM.le⟩, fun x y => ?_⟩
  have hBy := hbound (F (x.1 + y.1, x.2 + (y.2 : AddCircle period))) (Set.mem_range_self _)
  change ‖fderiv ℝ (localFieldLift period (fieldFDeriv period f)
    (x.1 + y.1, x.2 + (y.2 : AddCircle period))) 0‖ ≤ M at hBy
  rw [fderiv_localFieldLift_shift, localFieldLift_fieldFDeriv] at hBy
  exact hBy

end FieldCalculus

omit [Fact (0 < period)] in
theorem translationPath_continuous (a : LiftTangent) : Continuous (translationPath period a) :=
  (coveringMap_isOpenQuotient period).isQuotientMap.continuous.comp
    (continuous_id.smul continuous_const)

omit [Fact (0 < period)] in
theorem translationPath_add (a : LiftTangent) (s t : ℝ) :
    translationPath period a (s + t) = translationPath period a s + translationPath period a t := by
  simp [translationPath, coveringMap, add_smul]

omit [Fact (0 < period)] in
theorem translationPath_neg (a : LiftTangent) (t : ℝ) :
    translationPath period a (-t) = -translationPath period a t := by
  simp [translationPath, coveringMap]

theorem translation_pairing (a : LiftDomain period) (f g : LiftL2 period) :
    ⟪translation period a f, g⟫_ℝ = ⟪f, translation period (-a) g⟫_ℝ := by
  have hi := (translation period a).inner_map_map f (translation period (-a) g)
  simpa only [translation_add, add_neg_cancel, translation_zero] using hi

omit [Fact (0 < period)] in
theorem compact_translation_support (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f) :
    ∃ K : Set (LiftDomain period), IsCompact K ∧ tsupport f ⊆ K ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x ∉ K, f (x + translationPath period a t) = 0 := by
  let K := (fun p : LiftDomain period × ℝ => p.1 - translationPath period a p.2) ''
    (tsupport f ×ˢ Set.Icc (-1 : ℝ) 1)
  have hK : IsCompact K := (hfc.isCompact.prod isCompact_Icc).image
    (continuous_fst.sub ((translationPath_continuous period a).comp continuous_snd))
  refine ⟨K, hK, ?_, ?_⟩
  · intro x hx
    refine ⟨(x, 0), ⟨hx, by constructor <;> norm_num⟩, ?_⟩
    simp
  · intro t ht x hx
    by_contra hn
    apply hx
    refine ⟨(x + translationPath period a t, t),
      ⟨subset_tsupport f (Function.mem_support.mpr hn), abs_le.mp ht⟩, ?_⟩
    simp

/-- The actual L² element represented by a smooth compact vector field. -/
def smoothFieldLp (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) : LiftL2 period :=
  ((smoothField_continuous period f hf).memLp_of_hasCompactSupport hfc).toLp f

theorem smoothFieldLp_ae (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    smoothFieldLp period f hfc hf =ᵐ[liftMeasure period] f :=
  ((smoothField_continuous period f hf).memLp_of_hasCompactSupport hfc).coeFn_toLp

/-- The L² element represented by the actual directional derivative of a compact test field. -/
def derivativeFieldLp (a : LiftTangent) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    LiftL2 period := (fieldDerivative_memLp period a f hfc hf).toLp (fieldDerivative period a f)

theorem derivativeFieldLp_ae (a : LiftTangent) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    derivativeFieldLp period a f hfc hf =ᵐ[liftMeasure period] fieldDerivative period a f :=
  (fieldDerivative_memLp period a f hfc hf).coeFn_toLp

omit [Fact (0 < period)] in
theorem field_translation_remainder (a : LiftTangent)
    (f : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (M : ℝ≥0)
    (hDD : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period f x)) y‖ ≤ M)
    (t : ℝ) (x : LiftDomain period) :
    ‖f (x + translationPath period a t) - f x - t • fieldDerivative period a f x‖ ≤
      (M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2 := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => localFieldLift period f x (u • a))
      (fderiv ℝ (localFieldLift period f x) (s • a) a) s := by
    intro s
    have hF := (((hf x).differentiable (by simp)) (s • a)).hasFDerivAt
    convert hF.comp_hasDerivAt s ((hasDerivAt_id s).smul_const a) using 1 <;>
      first | rfl | simp
  have hr := uniform_derivative_remainder
    (fun s => localFieldLift period f x (s • a))
    (fun s => fderiv ℝ (localFieldLift period f x) (s • a) a) hd (M * ‖a‖₊ ^ 2)
    (fun s => by simpa only [zero_smul, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      directionalDerivative_line_lipschitz (localFieldLift period f x) (hf x) M (hDD x) a s) t
  change ‖f (x.1 + (t • a).1, x.2 + ((t • a).2 : AddCircle period)) - f x -
    t • fieldDerivative period a f x‖ ≤ _
  simpa only [localFieldLift, zero_smul, Prod.fst_zero, Prod.snd_zero,
    AddCircle.coe_zero, add_zero, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm,
    fieldDerivative] using hr

theorem smoothFieldLp_translation_hasDerivAt (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (smoothFieldLp period f hfc hf)) (derivativeFieldLp period a f hfc hf) 0 := by
  obtain ⟨M, hM⟩ := compact_smooth_second_derivative_bound period f hfc hf
  obtain ⟨K, hK, hKf, hKshift⟩ := compact_translation_support period a f hfc
  let f₀ := smoothFieldLp period f hfc hf
  let df := derivativeFieldLp period a f hfc hf
  let χ : Lp ℝ 2 (liftMeasure period) :=
    indicatorConstLp 2 hK.isClosed.measurableSet hK.measure_ne_top (1 : ℝ)
  have hR : ∀ t : ℝ, |t| ≤ 1 →
      ‖translation period (translationPath period a t) f₀ - f₀ - t • df‖ ≤
        ((M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2) * ‖χ‖ := by
    intro t ht
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [translation_ae period (translationPath period a t) f₀,
      (measurePreserving_translation period (translationPath period a t)).quasiMeasurePreserving.ae
        (smoothFieldLp_ae period f hfc hf), smoothFieldLp_ae period f hfc hf,
      derivativeFieldLp_ae period a f hfc hf,
      Lp.coeFn_sub (translation period (translationPath period a t) f₀) f₀,
      Lp.coeFn_smul t df,
      Lp.coeFn_sub (translation period (translationPath period a t) f₀ - f₀) (t • df),
      (indicatorConstLp_coeFn (p := 2) (hs := hK.isClosed.measurableSet)
        (hμs := hK.measure_ne_top) (c := (1 : ℝ)))]
      with x hτ hfx hf₀ hdf hsub hsmul hrem hχ
    simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hrem
    rw [hrem, hsub, hsmul, hτ, hfx, hf₀, hdf]
    change ‖f (x + translationPath period a t) - f x -
      t • fieldDerivative period a f x‖ ≤ (M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2 * ‖χ x‖
    change χ x = _ at hχ
    rw [hχ]
    by_cases hx : x ∈ K
    · simpa only [Set.indicator_of_mem hx, norm_one, mul_one] using
        field_translation_remainder period a f hf M hM t x
    · have hxf : x ∉ tsupport f := fun h => hx (hKf h)
      have hdz : fieldDerivative period a f x = 0 := by
        change fieldFDeriv period f x a = 0
        rw [fieldFDeriv_zero_outside period f x hxf]
        rfl
      rw [hKshift t ht x hx, image_eq_zero_of_notMem_tsupport hxf, hdz,
        Set.indicator_of_notMem hx]
      simp
  apply (hasDerivAt_iff_tendsto
    (f := fun t => translation period (translationPath period a t) f₀)
    (f' := df) (x := (0 : ℝ))).mpr
  simp only [translationPath_zero, translation_zero, sub_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t => by positivity
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
    have ht' : |t| ≤ 1 := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht.le
    calc
      _ ≤ ‖t‖⁻¹ * (((M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2) * ‖χ‖) :=
        mul_le_mul_of_nonneg_left (hR t ht') (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ ((M : ℝ) * ‖a‖ ^ 2 * ‖χ‖) * |t| := by
        by_cases ht0 : t = 0
        · simp [ht0]
        · rw [Real.norm_eq_abs]
          have hta : |t| ≠ 0 := abs_ne_zero.mpr ht0
          field_simp
          ring_nf
          exact le_rfl
  · simpa only [Pi.mul_def, abs_zero, mul_zero] using
      (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

theorem translation_derivative_pairing (a : LiftTangent) (f f' g g' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (hg : HasDerivAt (fun t => translation period (translationPath period a t) g) g' 0) :
    ⟪f', g⟫_ℝ = -⟪f, g'⟫_ℝ := by
  have hleft : HasDerivAt (fun t =>
      ⟪translation period (translationPath period a t) f, g⟫_ℝ) ⟪f', g⟫_ℝ 0 := by
    simpa only [translationPath_zero, translation_zero, inner_zero_right, zero_add] using
      hf.inner ℝ (hasDerivAt_const (0 : ℝ) g)
  have hneg : HasDerivAt (fun t => translation period (translationPath period a (-t)) g) (-g') 0 :=
      by
    convert hg.scomp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg) (by simp) using 1 <;>
      first | rfl | simp
  have hright : HasDerivAt (fun t =>
      ⟪f, translation period (translationPath period a (-t)) g⟫_ℝ) (-⟪f, g'⟫_ℝ) 0 := by
    simpa only [inner_neg_right, inner_zero_left, add_zero] using
      (hasDerivAt_const (0 : ℝ) f).inner ℝ hneg
  have heq : (fun t => ⟪translation period (translationPath period a t) f, g⟫_ℝ) =
      fun t => ⟪f, translation period (translationPath period a (-t)) g⟫_ℝ := by
    funext t
    simpa only [translationPath_neg] using
      translation_pairing period (translationPath period a t) f g
  rw [heq] at hleft
  exact hleft.unique hright

/-- A strong L² translation derivative is the actual distributional derivative. -/
theorem strong_translation_derivative_weak (a : LiftTangent) (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (φ : LiftDomain period → Vector3) (hφc : HasCompactSupport φ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) :
    (∫ x, ⟪f' x, φ x⟫_ℝ ∂liftMeasure period) =
      -(∫ x, ⟪f x, fieldDerivative period a φ x⟫_ℝ ∂liftMeasure period) := by
  have hp := translation_derivative_pairing period a f f'
    (smoothFieldLp period φ hφc hφ) (derivativeFieldLp period a φ hφc hφ) hf
    (smoothFieldLp_translation_hasDerivAt period a φ hφc hφ)
  calc
    _ = ⟪f', smoothFieldLp period φ hφc hφ⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [smoothFieldLp_ae period φ hφc hφ] with x hx
      rw [hx]
    _ = -⟪f, derivativeFieldLp period a φ hφc hφ⟫_ℝ := hp
    _ = _ := by
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [derivativeFieldLp_ae period a φ hφc hφ] with x hx
      rw [hx]

theorem divergenceFree_translation_mem (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {f : LiftL2 period} (hf : f ∈ divergenceFreeSpace period κ m) :
    translation period a f ∈ divergenceFreeSpace period κ m := by
  intro g hg
  rw [real_inner_comm, translation_pairing, real_inner_comm]
  exact hf (translation period (-a) g) (gradientSpace_translation_mem period κ m (-a) hg)

theorem divergenceFree_translation_derivative (κ : ℝ) (m : Vector3) (a : LiftTangent)
    {f f' : LiftL2 period} (hf : f ∈ divergenceFreeSpace period κ m)
    (hder : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    f' ∈ divergenceFreeSpace period κ m := by
  have hlim := hder.tendsto_slope_zero
  simp only [zero_add, translationPath_zero, translation_zero] at hlim
  apply (gradientSpace period κ m).isClosed_orthogonal.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun t => (divergenceFreeSpace period κ m).smul_mem _
    ((divergenceFreeSpace period κ m).sub_mem
      (divergenceFree_translation_mem period κ m (translationPath period a t) hf) hf)

theorem pressure_has_weak_derivative (κ : ℝ) (m : Vector3) (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hAs : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x))
    (C D M : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C)
    (hDA : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D)
    (hDDA : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    ∃ p' : LiftL2 period,
      HasDerivAt (fun t => translation period (translationPath period a t)
        (liftedPressure period κ m A hA C hAb c hc hpos f)) p' 0 ∧
      p' ∈ gradientSpace period κ m ∧
      ‖p'‖ ≤ c⁻¹ * (‖f'‖ + (D : ℝ) * ‖a‖ *
        ‖liftedPressure period κ m A hA C hAb c hc hpos f‖) ∧
      ∀ (φ : LiftDomain period → Vector3), HasCompactSupport φ →
        (∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) →
        (∫ x, ⟪p' x, φ x⟫_ℝ ∂liftMeasure period) =
          -(∫ x, ⟪(liftedPressure period κ m A hA C hAb c hc hpos f) x,
            fieldDerivative period a φ x⟫_ℝ ∂liftMeasure period) := by
  let p := liftedPressure period κ m A hA C hAb c hc hpos f
  let p' := liftedPressure period κ m A hA C hAb c hc hpos
    (f' - EulerLiftedPressure.coefficientOperator (translatedCoefficientDerivative period a A 0)
      (translatedCoefficientDerivative_measurable period a A hAs) (D * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A D hDA x) p)
  have hpd : HasDerivAt (fun t => translation period (translationPath period a t) p) p' 0 :=
    pressure_translation_hasDerivAt period κ m a A hA hAs C D M hAb hDA hDDA
      c hc hpos f f' hf
  refine ⟨p', hpd, liftedPressure_mem period κ m A hA C hAb c hc hpos _, ?_, ?_⟩
  · have hn := pressure_translation_derivative_norm period κ m a A hA hAs C D M hAb hDA hDDA
      c hc hpos f f' hf
    rwa [hpd.deriv] at hn
  · intro φ hφc hφ
    exact strong_translation_derivative_weak period a p p' hpd φ hφc hφ

end EulerLiftedWeakDerivative
