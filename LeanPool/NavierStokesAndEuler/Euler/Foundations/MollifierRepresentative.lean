/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderMollifier
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SetIntegralL2
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Actual classical smooth representatives of the strong L² cylinder mollifiers. -/

section

/-! Classical smooth cylinder representatives obtained by Euclidean mollification. -/

@[expose] public section

noncomputable section

namespace EulerCoverMollification

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerLiftedGradientSpace
    EulerMetricTransport
open scoped ContDiff ENNReal Convolution Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem euclideanCover_add (z w : Domain 4) :
    euclideanCover period (z+w) = euclideanCover period z + euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_add]

omit [Fact (0 < period)] in
theorem euclideanCover_sub (z w : Domain 4) :
    euclideanCover period (z-w) = euclideanCover period z - euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_sub]

omit [Fact (0 < period)] in
theorem euclideanCover_surjective : Function.Surjective (euclideanCover period) := by
  intro x
  obtain ⟨v, hv⟩ := (coveringMap_isOpenQuotient period).surjective x
  refine ⟨coordinateEquiv.symm v, ?_⟩
  simpa only [euclideanCover, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hv

section Integrability
variable {F : Type*} [NormedAddCommGroup F]

/-- L² cylinder fields have locally integrable periodic lifts to the Euclidean covering space. -/
theorem locallyIntegrable_cover (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) :
    LocallyIntegrable (f ∘ euclideanCover period) (volume : Measure (Domain 4)) := by
  intro x
  have hT : 0 < period := Fact.out
  let a : ℝ := x 0 - period/2
  have hsubset : Metric.ball x (period/4) ⊆ {z : Domain 4 | z 0 ∈ Set.Ioc a (a+period)} := by
    intro z hz
    have hd : ‖z-x‖ < period/4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hc : |z 0-x 0| ≤ ‖z-x‖ := PiLp.norm_apply_le (z-x) 0
    have hh := abs_le.mp (hc.trans hd.le)
    change a < z 0 ∧ z 0 ≤ a+period
    dsimp [a]
    constructor <;> linarith
  have hmeasure : (volume : Measure (Domain 4)).restrict (Metric.ball x (period/4)) ≤ stripMeasure
      period a :=
    Measure.restrict_mono hsubset le_rfl
  have hb : MemLp (f ∘ euclideanCover period) 2
      ((volume : Measure (Domain 4)).restrict (Metric.ball x (period/4))) :=
    MemLp.mono_measure hmeasure (memLp_cover period f hf a)
  have : Fact ((volume : Measure (Domain 4)) (Metric.ball x (period/4)) < ⊤) :=
      ⟨measure_ball_lt_top⟩
  exact ⟨Metric.ball x (period/4), Metric.ball_mem_nhds x (by
      positivity), hb.integrable (by norm_num)⟩

end Integrability

section Convolution
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Euclidean convolution of the periodic lift with a normalized compact bump. -/
noncomputable def coverConvolution (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F) :
    Domain 4 → F :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f ∘ euclideanCover period)

/-- The same convolution defined directly on the cylinder, with the usual negative translation. -/
noncomputable def cylinderConvolution (φ : ContDiffBump (0 : Domain 4))
    (f : LiftDomain period → F) (x : LiftDomain period) : F :=
  ∫ y : Domain 4, φ.normed volume y • f (x - euclideanCover period y)

omit [Fact (0 < period)] [CompleteSpace F] in
theorem cylinderConvolution_cover (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (z : Domain 4) :
    cylinderConvolution period φ f (euclideanCover period z) = coverConvolution period φ f z := by
  rw [coverConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply, Function.comp_apply, euclideanCover_sub]

omit [CompleteSpace F] in
/-- The classical covering-space convolution is genuinely C∞. -/
theorem coverConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) : ContDiff ℝ ∞ (coverConvolution period φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (n := (⊤ : ℕ∞))) (locallyIntegrable_cover period f hf)

omit [CompleteSpace F] in
/-- The convolution descends to a C∞ cylinder field in the actual local covering coordinates. -/
theorem cylinderConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (cylinderConvolution period φ f) x) := by
  intro x
  obtain ⟨z, hz⟩ := euclideanCover_surjective period x
  have he : localFieldLift period (cylinderConvolution period φ f) x =
      fun v => coverConvolution period φ f (z + coordinateEquiv.symm v) := by
    funext v
    rw [← cylinderConvolution_cover, euclideanCover_add, hz]
    congr 1
  rw [he]
  exact (coverConvolution_smooth period φ f hf).comp (contDiff_const.add
      coordinateEquiv.symm.contDiff)

omit [Fact (0 < period)] [CompleteSpace F] in
/-- The covering-space convolution is periodic in the angular direction. -/
theorem coverConvolution_periodic (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F) :
    Function.Periodic (coverConvolution period φ f) (EuclideanSpace.single 0 period) := by
  intro z
  rw [← cylinderConvolution_cover, ← cylinderConvolution_cover, euclideanCover_add]
  have hz : euclideanCover period (EuclideanSpace.single 0 period) = 0 := by
    apply Prod.ext
    · ext i
      simp [euclideanCover, coveringMap]
    · simp [euclideanCover, coveringMap]
  rw [hz, add_zero]

/-- Normalized shrinking bump convolutions recover the original covering-space function almost
everywhere. -/
theorem ae_coverConvolution_tendsto {φ : ℕ → ContDiffBump (0 : Domain 4)}
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hshape : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 2 * (φ n).rIn)
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) :
    ∀ᵐ z ∂(volume : Measure (Domain 4)), Filter.Tendsto (fun n => coverConvolution period (φ n) f z)
      Filter.atTop (𝓝 (f (euclideanCover period z))) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hshape (locallyIntegrable_cover
      period f hf)

end Convolution
end EulerCoverMollification

end
end

end

section

/-! The finite-set Fubini bridge identifying classical and L² cylinder mollification. -/

@[expose] public section

noncomputable section

namespace EulerCoverMollificationFubini

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCoverMollification
    EulerLiftedGradientSpace
open scoped ENNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The elementary L²-to-L¹ bound on an arbitrary finite-measure set. -/
theorem finite_set_integral_norm_le (f : LiftDomain period → Vector3)
    (hf : MemLp f 2 (liftMeasure period)) (K : Set (LiftDomain period))
    (hK : liftMeasure period K < ⊤) :
    (∫ x in K, ‖f x‖ ∂liftMeasure period) ≤
      (eLpNorm f 2 (liftMeasure period)).toReal * (liftMeasure period K).toReal ^ (1/2 : ℝ) := by
  have hA := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (1 : ℝ≥0∞)) (q := 2)
    (by norm_num) (hf.restrict K).1
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div, inv_one,
      Measure.restrict_apply_univ] at hA
  have hB : eLpNorm f 2 ((liftMeasure period).restrict K) * (liftMeasure period K)^(1/2 : ℝ) ≤
      eLpNorm f 2 (liftMeasure period) * (liftMeasure period K)^(1/2 : ℝ) :=
    mul_le_mul' (eLpNorm_mono_measure f (Measure.restrict_le_self (s := K))) le_rfl
  have hfin : eLpNorm f 2 (liftMeasure period) * (liftMeasure period K) ^ (1/2 : ℝ) ≠ ⊤ := by
      finiteness
  have hC := ENNReal.toReal_mono hfin (hA.trans hB)
  rw [integral_norm_eq_lintegral_enorm (hf.restrict K).1, ← eLpNorm_one_eq_lintegral_enorm]
  convert hC using 1
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

omit [Fact (0 < period)] in
/-- The Euclidean covering map is continuous. -/
theorem euclideanCover_continuous : Continuous (euclideanCover period) :=
  (coveringMap_isOpenQuotient period).isQuotientMap.continuous.comp coordinateEquiv.continuous

/-- The convolution kernel is jointly integrable over the kernel variable and any finite cylinder
set. -/
theorem kernel_integrable_prod (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    Integrable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1))
      ((volume : Measure (Domain 4)).prod ((liftMeasure period).restrict K)) := by
  have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
  have hmap : Measurable (fun p : Domain 4 × LiftDomain period => p.2 - euclideanCover period p.1)
      :=
    (continuous_snd.sub ((euclideanCover_continuous period).comp continuous_fst)).measurable
  have hsm : StronglyMeasurable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1)) :=
    ((φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.comp continuous_fst).stronglyMeasurable.smul
      ((Lp.stronglyMeasurable U).comp_measurable hmap)
  have hshift (y : Domain 4) : MemLp (fun x => U (x - euclideanCover period y)) 2 (liftMeasure
      period) := by
    convert! (Lp.memLp U).comp_measurePreserving
      (measurePreserving_translation period (-euclideanCover period y)) using 1
  apply (integrable_prod_iff hsm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with y
    have hint : Integrable (fun x => U (x-euclideanCover period y)) ((liftMeasure period).restrict
        K) :=
      ((hshift y).restrict K).integrable (by norm_num)
    exact hint.smul (φ.normed volume y)
  · have hbound (y : Domain 4) : (∫ x in K, ‖φ.normed volume y • U (x - euclideanCover period y)‖
      ∂liftMeasure period) ≤
        ‖φ.normed volume y‖ * (‖U‖ * (liftMeasure period K).toReal ^ (1/2 : ℝ)) := by
      simp only [norm_smul, integral_const_mul]
      have he : eLpNorm (fun x => U (x - euclideanCover period y)) 2 (liftMeasure period) =
          eLpNorm U 2 (liftMeasure period) := by
        simpa only [Function.comp_def, sub_eq_add_neg] using
          eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) (Lp.aestronglyMeasurable U)
            (measurePreserving_translation period (-euclideanCover period y))
      have h := finite_set_integral_norm_le period _ (hshift y) K hK
      rw [he, ← Lp.norm_def] at h
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    exact (φ.integrable_normed.norm.mul_const (‖U‖ * (liftMeasure period K).toReal ^ (1/2 :
        ℝ))).mono'
      hsm.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
        exact hbound y))

/-- The classical cylinder convolution is integrable on each finite-measure set. -/
theorem cylinderConvolution_integrableOn (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    IntegrableOn (cylinderConvolution period φ U) K (liftMeasure period) := by
  exact (kernel_integrable_prod period φ U K hK).integral_prod_right

/-- Exact Fubini identity for every finite cylinder set. -/
theorem setIntegral_cylinderConvolution (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    (∫ x in K, cylinderConvolution period φ U x ∂liftMeasure period) =
      ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure
          period) := by
  have h := integral_integral_swap (f := fun (y : Domain 4) (x : LiftDomain period) =>
      φ.normed volume y • U (x-euclideanCover period y))
    (μ := (volume : Measure (Domain 4))) (ν := (liftMeasure period).restrict K)
    (kernel_integrable_prod period φ U K hK)
  change (∫ x in K, ∫ y : Domain 4, φ.normed volume y • U (x-euclideanCover period y) ∂volume
      ∂liftMeasure period) = _
  rw [← h]
  simp only [integral_smul]

/-- Equality of finite-set integrals identifies a Bochner L² mollifier with the classical smooth
field. -/
theorem ae_eq_cylinderConvolution_of_setIntegrals (φ : ContDiffBump (0 : Domain 4)) (U V : LiftL2
    period)
    (hV : ∀ K : Set (LiftDomain period), MeasurableSet K → liftMeasure period K < ⊤ →
      (∫ x in K, V x ∂liftMeasure period) =
        ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure
            period)) :
    (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] cylinderConvolution period φ U := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro K _ hK
    have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
    exact ((Lp.memLp V).restrict K).integrable (by norm_num)
  · intro K _ hK
    exact cylinderConvolution_integrableOn period φ U K hK
  · intro K hK hfin
    exact (hV K hK hfin).trans (setIntegral_cylinderConvolution period φ U K hfin).symm

end EulerCoverMollificationFubini

end
end

end

@[expose] public section

noncomputable section

namespace EulerMollifierRepresentative

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev
open EulerLiftedGradientSpace EulerMetricTransport EulerCoverMollification
open EulerCoverMollificationFubini EulerCylinderMollifier EulerSpatialSobolevInverse
    EulerStrongSmoothJet
open scoped ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The concrete classical convolution representing the Bochner L² mollifier. -/
noncomputable def smoothMollifier (n : ℕ) (U : LiftL2 period) : LiftDomain period → Vector3 :=
  cylinderConvolution period (mollifierBump n) U

/-- The smooth convolution and the Bochner convolution are the same almost everywhere. -/
theorem mollify_ae_smoothMollifier (n : ℕ) (U : LiftL2 period) :
    (mollify period n U : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      smoothMollifier period n U := by
  apply ae_eq_cylinderConvolution_of_setIntegrals period (mollifierBump n) U (mollify period n U)
  intro K hK hfin
  simpa only [mollifierKernel, integral_smul] using
    EulerSetIntegralL2.mollify_setIntegral period n U K hK hfin.ne

/-- Every strong L² mollifier has an actual C∞ representative on the cylinder. -/
theorem smoothMollifier_smooth (n : ℕ) (U : LiftL2 period) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (smoothMollifier period n U) x) :=
  cylinderConvolution_smooth period (mollifierBump n) U (Lp.memLp U)

/-- Strong mollified jets are precisely the classical derivatives of the smooth convolution. -/
theorem smoothMollifier_word_ae {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    (mollify period n (J.word w) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      iteratedFieldDerivative period w (smoothMollifier period n U) := by
  rw [← mollifyJet_word period J n w]
  exact jet_word_ae period hk _ (mollifyJet period J n) w _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

/-- All available classical derivatives of the smooth mollifier are genuinely in L². -/
theorem smoothMollifier_word_memLp {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    MemLp (iteratedFieldDerivative period w (smoothMollifier period n U)) 2 (liftMeasure period) :=
  (Lp.memLp _).ae_eq (smoothMollifier_word_ae period hk U J n w)

/-- The strong and classical Sobolev norms of each mollifier agree exactly. -/
theorem smoothMollifier_sobolevNorm {s : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) :
    (mollifyJet period J n).sobolevNorm = liftSobolevNorm period s (smoothMollifier period n U) :=
  jet_sobolevNorm_eq period _ (mollifyJet period J n) _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

end EulerMollifierRepresentative
