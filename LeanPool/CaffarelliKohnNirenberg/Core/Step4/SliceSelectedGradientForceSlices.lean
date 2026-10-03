/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryForceSlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SupportRestrict

/-!
# Slice Selected Gradient Force Slices

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-!
# The slice data of the two force potentials of `eq:pk`

The local pressure decomposition `eq:pk` carries the force through the two potentials
`pressureP7 η f s` and `pressureP8 η f s` of `CKN.Pressure.DecompositionPotentials`,
whose densities on a time slice are `η y * f (y, s) j` and
`spatialDeriv η j y * f (y, s) j`.  Display (3.5) of the pressure-gradient section
differentiates these potentials on the inner ball of `η`, and therefore needs, on almost
every time slice of a suitable weak solution in the sense of `def:sws`: the `L^{6/5}`
membership and compact support of the first density, the integrability of the second
density, and an `L¹` bound for the second density in terms of the force on the ball.

The first fact is an immediate consequence of the compact support of the cutoff.  The
second and third transfer the slice membership of the force, supplied by
`sws_force_memLp_slice_ae`, to the two densities: the cutoff is bounded by one, so the
first density inherits every `L^p` bound of the force, while the derivative of the cutoff
is bounded by `cutoffGradientConstant / ρ`, which gives both the integrability of the
second density and its `L¹` estimate.
-/

/-- The Euclidean length on the native carrier is continuous, being the norm of the
`L²` representative of a vector. -/
private theorem continuous_vec3EuclideanNorm :
    Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
  rw [show (fun v : Vec3 => vec3EuclideanNorm v) = fun v => ‖WithLp.toLp 2 v‖ by
    funext v
    exact vec3EuclideanNorm_eq_l2 v]
  exact continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))

/-- The Euclidean length on the native carrier is controlled by the ambient sup norm. -/
private theorem vec3EuclideanNorm_le_three_mul_norm (v : Vec3) :
    vec3EuclideanNorm v ≤ 3 * ‖v‖ := by
  simpa only [vec3EuclideanNorm, CKN.spaceEuclideanNorm] using
    CKN.euclideanNorm_le_three_mul_space_norm v

/-- The native Euclidean length agrees with the one used by the finite-sum carrier. -/
private theorem vecEuclideanNorm_eq_vec3_local (v : Vec3) :
    vecEuclideanNorm v = vec3EuclideanNorm v := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The ball has finite Lebesgue measure, so the Lebesgue measure restricted to it is a
finite measure.  This is what lets a slice membership of the force be lowered from `L^q`
to `L¹` on the ball. -/
private theorem isFiniteMeasure_restrict_vec3Ball (x₀ : Vec3) (ρ : ℝ) :
    IsFiniteMeasure (volume.restrict (vec3Ball x₀ ρ)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x₀) (r := ρ)⟩

/-- The gradient constant divided by the radius is nonnegative: the bound on a single
coordinate derivative of the cutoff already forces this. -/
private theorem cutoffGradientConstant_div_nonneg (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ cutoffGradientConstant / ρ := by
  have h := pressure_cutoff_spatialDeriv_bound x₀ hρ x₀ (0 : Fin 3)
  exact (abs_nonneg _).trans h

/-- An `L^p` function on a restricted measure whose support is contained in the
restricting set is `L^p` on the full measure. -/
private theorem memLp_volume_of_memLp_restrict_of_support_q
    {h : Vec3 → ℝ} {s : Set Vec3} {q : ℝ}
    (hmeas : AEStronglyMeasurable h volume) (hsupp : Function.support h ⊆ s)
    (hh : MemLp h (ENNReal.ofReal q) (volume.restrict s)) :
    MemLp h (ENNReal.ofReal q) volume := by
  rw [memLp_iff] at hh ⊢
  rwa [eLpNorm_restrict_eq_of_support_subset hmeas hsupp] at hh

/-- On a slice on which the force is `L^q` about the ball, the two densities of the force
potentials of `eq:pk` carry the corresponding data: the first is `L^q` on the whole
space, the second is integrable, and the `L¹` size of the second is bounded by the
gradient constant of the cutoff divided by the radius times the `L¹` size of the force on
the ball. -/
private theorem slice_force_sources_local
    (x₀ : Vec3) {ρ q s : ℝ} (hρ : 0 < ρ) (hq : 6 / 5 ≤ q)
    {f : ParabolicPoint → Vec3}
    (hf : MemLp (fun x : Vec3 => f (x, s)) (ENNReal.ofReal q)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hint : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (f (y, s)))
      (vec3Ball x₀ ρ) volume) :
    (∀ j : Fin 3, MemLp
        (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
        (ENNReal.ofReal q) volume) ∧
      (∀ j : Fin 3, Integrable
        (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
        volume) ∧
      (∀ j : Fin 3, (∫ y : Vec3,
          ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖) ≤
        (cutoffGradientConstant / ρ) *
          ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) := by
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff x₀ hρ) :=
    mollifiedBallCutoff_smooth x₀ hρ
  have hηsupport : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ vec3Ball x₀ ρ :=
    pressure_cutoff_support_subset_ball x₀ hρ
  have hηbound : ∀ y, |mollifiedBallCutoff x₀ hρ y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x₀ hρ y)]
    exact mollifiedBallCutoff_le_one x₀ hρ y
  have hηderiv : ∀ j y, |spatialDeriv (mollifiedBallCutoff x₀ hρ) j y| ≤
      cutoffGradientConstant / ρ :=
    fun j y => pressure_cutoff_spatialDeriv_bound x₀ hρ y j
  have hηmeas : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ) volume :=
    hηsmooth.continuous.aestronglyMeasurable
  have hq1 : 1 ≤ q := by linarith only [hq]
  have hsource₇ : ∀ j : Fin 3, AEStronglyMeasurable
      (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume := by
    intro j
    have hηB : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ)
        (volume.restrict (vec3Ball x₀ ρ)) :=
      hηmeas.mono_measure Measure.restrict_le_self
    have hcompB : AEStronglyMeasurable (fun y : Vec3 => f (y, s) j)
        (volume.restrict (vec3Ball x₀ ρ)) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
          hf.aestronglyMeasurable
    have hmulB : AEStronglyMeasurable
        (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
        (volume.restrict (vec3Ball x₀ ρ)) := hηB.mul hcompB
    refine CKN.Foundation.Measure.aestronglyMeasurable_of_restrict_of_support
      (vec3Ball_measurable x₀ ρ) hmulB ?_
    intro y hy
    by_contra hyB
    apply hy
    change mollifiedBallCutoff x₀ hρ y * f (y, s) j = 0
    have hzero : mollifiedBallCutoff x₀ hρ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hηy => hyB (hηsupport hηy))
    rw [hzero, zero_mul]
  have hcomp (j : Fin 3) : MemLp (fun y : Vec3 => f (y, s) j)
      (ENNReal.ofReal q) (volume.restrict (vec3Ball x₀ ρ)) := by
    apply hf.of_le
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hf.aestronglyMeasurable)
    filter_upwards [] with y
    change ‖f (y, s) j‖ ≤ ‖f (y, s)‖
    exact norm_le_pi_norm (f (y, s)) j
  have hsource₇_support (j : Fin 3) :
      Function.support
        (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) ⊆
        vec3Ball x₀ ρ := by
    intro y hy
    by_contra hyB
    apply hy
    change mollifiedBallCutoff x₀ hρ y * f (y, s) j = 0
    have hzero : mollifiedBallCutoff x₀ hρ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hηy => hyB (hηsupport hηy))
    rw [hzero, zero_mul]
  have hsource₈_support (j : Fin 3) :
      Function.support
        (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) ⊆
        vec3Ball x₀ ρ := by
    intro y hy
    by_contra hyB
    apply hy
    change spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j = 0
    have hzero : spatialDeriv (mollifiedBallCutoff x₀ hρ) j y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hηy => hyB
        ((tsupport_fderiv_apply_subset ℝ (CKN.basisVec j)).trans hηsupport hηy))
    rw [hzero, zero_mul]
  have hsource₇_mem (j : Fin 3) : MemLp
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
      (ENNReal.ofReal q) (volume.restrict (vec3Ball x₀ ρ)) := by
    apply (hcomp j).of_le
      ((hsource₇ j).mono_measure Measure.restrict_le_self)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs, one_mul] using
      (mul_le_mul_of_nonneg_right (hηbound y) (abs_nonneg (f (y, s) j)))
  have hsource₇_mem_global (j : Fin 3) : MemLp
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
      (ENNReal.ofReal q) volume :=
    memLp_volume_of_memLp_restrict_of_support_q
      (hsource₇ j) (hsource₇_support j) (hsource₇_mem j)
  have hderiv_meas (j : Fin 3) : AEStronglyMeasurable
      (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) volume :=
    (contDiff_spatialDeriv_smooth hηsmooth j).continuous.aestronglyMeasurable
  have hsource₈_int (j : Fin 3) : Integrable
      (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
      volume := by
    have hmul : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict (vec3Ball x₀ ρ)) :=
      letI := isFiniteMeasure_restrict_vec3Ball x₀ ρ
      (hcomp j).integrable (ENNReal.one_le_ofReal.2 hq1)
    have hderiv_meas_B : AEStronglyMeasurable
        (spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (volume.restrict (vec3Ball x₀ ρ)) :=
      (hderiv_meas j).mono_measure Measure.restrict_le_self
    have hmul' := hmul.mul_bdd hderiv_meas_B
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using hηderiv j y))
    have hmul'' : Integrable
        (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
        (volume.restrict (vec3Ball x₀ ρ)) := by
      simpa only [mul_comm] using hmul'
    exact decomposition_full_of_on_sws hmul''
      ((tsupport_mul_subset_left (f := spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (g := fun y : Vec3 => f (y, s) j)).trans
          ((tsupport_fderiv_apply_subset ℝ (CKN.basisVec j)).trans hηsupport))
  have hbound (j : Fin 3) :
      (∫ y : Vec3, ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖) ≤
        (cutoffGradientConstant / ρ) *
          ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) := by
    have hcρ : 0 ≤ cutoffGradientConstant / ρ := cutoffGradientConstant_div_nonneg x₀ hρ
    have hvan : ∀ y : Vec3, y ∉ vec3Ball x₀ ρ →
        ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖ = 0 := by
      intro y hy
      have hz : spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j = 0 := by
        by_contra hne
        exact hy (hsource₈_support j hne)
      rw [hz, norm_zero]
    have hleft : (∫ y : Vec3,
        ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖) =
        ∫ y in vec3Ball x₀ ρ,
          ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
    rw [hleft]
    have hpoint : ∀ y ∈ vec3Ball x₀ ρ,
        ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖ ≤
          (cutoffGradientConstant / ρ) * vec3EuclideanNorm (f (y, s)) := by
      intro y _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hηderiv j y) (by
          rw [← vecEuclideanNorm_eq_vec3_local]
          exact abs_apply_le_vecEuclideanNorm (f (y, s)) j)
        (abs_nonneg _) hcρ
    calc
      ∫ y in vec3Ball x₀ ρ, ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖
          ≤ ∫ y in vec3Ball x₀ ρ,
              (cutoffGradientConstant / ρ) * vec3EuclideanNorm (f (y, s)) :=
            setIntegral_mono_on ((hsource₈_int j).norm.integrableOn)
              (hint.const_mul (cutoffGradientConstant / ρ))
              (vec3Ball_measurable x₀ ρ) hpoint
      _ = (cutoffGradientConstant / ρ) *
            ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) := by
            rw [integral_const_mul]
  exact ⟨fun j => hsource₇_mem_global j, fun j => hsource₈_int j, fun j => hbound j⟩

/-- The first density `η y * f (y, s) j` of the force potentials `pressureP7 η f s` and
`pressureP8 η f s` of `eq:pk` has compact support, so that it is a legitimate source for
the Newtonian potentials of display (3.5) of the pressure-gradient section. -/
theorem hasCompactSupport_cutoff_mul_force
    (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (f : ParabolicPoint → Vec3) (s : ℝ) (j : Fin 3) :
    HasCompactSupport (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) := by
  change HasCompactSupport (mollifiedBallCutoff x₀ hρ * fun y : Vec3 => f (y, s) j)
  exact (mollifiedBallCutoff_hasCompactSupport x₀ hρ).mul_right

/-- The slice data of the two force densities of `eq:pk` on a ball, given only that the
force is `L^q` on that ball for some `q ≥ 6/5`: the force itself is `L¹` there, the first
density is `L^{6/5}` on the whole space, the second density is integrable, and its `L¹`
size is controlled by `cutoffGradientConstant / ρ` times the `L¹` size of the force on
the ball.  These are the hypotheses that display (3.5) of the pressure-gradient section
uses when differentiating the potentials `pressureP7 η f s` and `pressureP8 η f s`. -/
theorem slice_force_source_data_of_memLp
    {x₀ : Vec3} {ρ q s : ℝ} (hρ : 0 < ρ) (hq : 6 / 5 ≤ q)
    {f : ParabolicPoint → Vec3}
    (hf : MemLp (fun x : Vec3 => f (x, s)) (ENNReal.ofReal q)
      (volume.restrict (vec3Ball x₀ ρ))) :
    IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (f (y, s)))
        (vec3Ball x₀ ρ) volume ∧
      (∀ j : Fin 3, MemLp (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ j : Fin 3, Integrable
        (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
        volume) ∧
      (∀ j : Fin 3, (∫ y : Vec3,
          ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖) ≤
        (cutoffGradientConstant / ρ) *
          ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) := by
  have hq1 : 1 ≤ q := by linarith only [hq]
  have hint : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (f (y, s)))
      (vec3Ball x₀ ρ) volume := by
    have hnorm : Integrable (fun y : Vec3 => ‖f (y, s)‖)
        (volume.restrict (vec3Ball x₀ ρ)) :=
      letI := isFiniteMeasure_restrict_vec3Ball x₀ ρ
      (hf.integrable (ENNReal.one_le_ofReal.2 hq1)).norm
    have hbound : Integrable (fun y : Vec3 => 3 * ‖f (y, s)‖)
        (volume.restrict (vec3Ball x₀ ρ)) := hnorm.const_mul 3
    refine hbound.mono' ?_ ?_
    · exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hf.aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact vec3EuclideanNorm_le_three_mul_norm _
  obtain ⟨hmem, hint_der, hbound⟩ := slice_force_sources_local x₀ hρ hq hf hint
  refine ⟨hint, ?_, hint_der, hbound⟩
  intro j
  have hcs : HasCompactSupport
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) :=
    hasCompactSupport_cutoff_mul_force x₀ hρ f s j
  exact (hmem j).mono_exponent_of_measure_support_ne_top
    (s := tsupport (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j))
    (fun y hy => image_eq_zero_of_notMem_tsupport
      (f := fun z : Vec3 => mollifiedBallCutoff x₀ hρ z * f (z, s) j) hy)
    hcs.isCompact.measure_lt_top.ne
    (ENNReal.ofReal_le_ofReal hq)

/-- The slice data of the two force densities of `eq:pk` holds on almost every time slice
of the lower half of a parabolic cylinder whose closure lies in the carrier of a suitable
weak solution: the force is `L^q` there with `q > 5/2`, hence `L^1`, the first density is
`L^{6/5}` on the whole space, the second density is integrable, and its `L¹` size is
controlled by `cutoffGradientConstant / ρ` times the `L¹` size of the force on the ball.
This is the almost-everywhere statement that display (3.5) of the pressure-gradient
section presupposes when it differentiates `pressureP7 η f s` and `pressureP8 η f s`. -/
theorem slice_force_source_data_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (f (y, s)))
          (vec3Ball z.1 ρ) volume ∧
        (∀ j : Fin 3, MemLp (fun y : Vec3 => mollifiedBallCutoff z.1 hρ y * f (y, s) j)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
        (∀ j : Fin 3, Integrable
          (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff z.1 hρ) j y * f (y, s) j)
          volume) ∧
        (∀ j : Fin 3, (∫ y : Vec3,
            ‖spatialDeriv (mollifiedBallCutoff z.1 hρ) j y * f (y, s) j‖) ≤
          (cutoffGradientConstant / ρ) *
            ∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (f (y, s))) := by
  have hq : 6 / 5 ≤ q := by linarith only [hsol.2.2.2.1]
  filter_upwards [sws_force_memLp_slice_ae hsol hρ hsub] with s hs
  exact slice_force_source_data_of_memLp (x₀ := z.1) hρ hq hs

end CKN.Core.Step4
