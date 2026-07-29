/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredRepresentative
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Filter Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors Topology

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
theorem norm_logarithmicMellinWeight
    (s : ℂ) (y : mixedEmbedding.realSpace K) :
    ‖logarithmicMellinWeight K s y‖ =
      Real.exp (y w₀ * (Module.finrank ℚ K : ℝ) * s.re) := by
  rw [logarithmicMellinWeight, norm_exp]
  simp

omit [IsTotallyComplex K] in
open Classical in
theorem norm_logarithmicMellinWeight_mono
    {s : ℂ} {b : ℝ} {y : mixedEmbedding.realSpace K}
    (hy : 0 ≤ y w₀) (hsb : s.re ≤ b) :
    ‖logarithmicMellinWeight K s y‖ ≤
      ‖logarithmicMellinWeight K (b : ℂ) y‖ := by
  rw [norm_logarithmicMellinWeight,
    norm_logarithmicMellinWeight]
  apply Real.exp_le_exp.mpr
  simp only [ofReal_re]
  have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hsb (mul_nonneg hy hn)

omit [IsTotallyComplex K] in
open Classical in
theorem norm_centeredNonzeroFractionalShapeThetaMellinKernel_mono
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} {b : ℝ} {y : mixedEmbedding.realSpace K}
    (hy : 0 ≤ y w₀) (hsb : s.re ≤ b) :
    ‖centeredNonzeroFractionalShapeThetaMellinKernel K I s y‖ ≤
      ‖centeredNonzeroFractionalShapeThetaMellinKernel K I (b : ℂ) y‖ := by
  rw [centeredNonzeroFractionalShapeThetaMellinKernel,
    centeredNonzeroFractionalShapeThetaMellinKernel,
    norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_logarithmicMellinWeight_mono K hy hsb) (norm_nonneg _)

open Classical in
/-- A centered mellin radial coefficient used in the Odlyzko-bound argument. -/
noncomputable def centeredMellinRadialCoefficient
    (y : mixedEmbedding.realSpace K) : ℂ :=
  (y w₀ * (Module.finrank ℚ K : ℝ) : ℝ)

omit [IsTotallyComplex K] in
open Classical in
theorem hasDerivAt_centeredNonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) :
    HasDerivAt
      (fun z ↦ centeredNonzeroFractionalShapeThetaMellinKernel K I z y)
      (centeredMellinRadialCoefficient K y *
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y) s := by
  let c : ℂ := (y w₀ * (Module.finrank ℚ K : ℝ) : ℝ)
  let A : ℂ :=
    fractionalShapeIdealTheta K I
      (expMapBasis (centeredFractionalShapeCoordinates K I y))
      (fun w ↦
        (expMapBasis_pos
          (centeredFractionalShapeCoordinates K I y) w).ne') - 1
  change HasDerivAt (fun z ↦ Complex.exp (c * z) * A)
    (c * (Complex.exp (c * s) * A)) s
  simpa only [id_eq, one_mul, mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id s).const_mul c).cexp.mul_const A)

omit [IsTotallyComplex K] in
open Classical in
theorem norm_centeredMellinRadialCoefficient_mul_kernel_le
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} {b : ℝ} {y : mixedEmbedding.realSpace K}
    (hy : 0 ≤ y w₀) (hsb : s.re + 1 ≤ b) :
    ‖centeredMellinRadialCoefficient K y *
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y‖ ≤
      ‖centeredNonzeroFractionalShapeThetaMellinKernel K I (b : ℂ) y‖ := by
  let t : ℝ := y w₀ * (Module.finrank ℚ K : ℝ)
  have ht : 0 ≤ t := mul_nonneg hy (by positivity)
  have htexp : t ≤ Real.exp t :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp t)
  have hweight :
      t * Real.exp (t * s.re) ≤ Real.exp (t * b) := by
    calc
      t * Real.exp (t * s.re) ≤ Real.exp t * Real.exp (t * s.re) :=
        mul_le_mul_of_nonneg_right htexp (Real.exp_pos _).le
      _ = Real.exp (t * (s.re + 1)) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (t * b) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsb ht)
  rw [norm_mul, centeredMellinRadialCoefficient, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht,
    centeredNonzeroFractionalShapeThetaMellinKernel,
    centeredNonzeroFractionalShapeThetaMellinKernel,
    norm_mul, norm_mul, norm_logarithmicMellinWeight,
    norm_logarithmicMellinWeight]
  simp only [Complex.ofReal_re]
  dsimp [t] at hweight
  calc
    _ = (y w₀ * (Module.finrank ℚ K : ℝ) *
          Real.exp (y w₀ * (Module.finrank ℚ K : ℝ) * s.re)) *
        ‖fractionalShapeIdealTheta K I
          (expMapBasis (centeredFractionalShapeCoordinates K I y))
          (fun w ↦
            (expMapBasis_pos
              (centeredFractionalShapeCoordinates K I y) w).ne') - 1‖ := by ring
    _ ≤ Real.exp (y w₀ * (Module.finrank ℚ K : ℝ) * b) *
        ‖fractionalShapeIdealTheta K I
          (expMapBasis (centeredFractionalShapeCoordinates K I y))
          (fun w ↦
            (expMapBasis_pos
              (centeredFractionalShapeCoordinates K I y) w).ne') - 1‖ :=
      mul_le_mul_of_nonneg_right hweight (norm_nonneg _)

open Classical in
theorem integrableOn_positive_centeredNonzeroFractionalShapeThetaMellinKernel_mk0
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    IntegrableOn
      (centeredNonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K J) s)
      (positiveUnitFundamentalParamSet (K := K)) := by
  let b : ℝ := max s.re 2 + 1
  let I := FractionalIdeal.mk0 K J
  let f := centeredNonzeroFractionalShapeThetaMellinKernel K I s
  let g := centeredNonzeroFractionalShapeThetaMellinKernel K I (b : ℂ)
  have : 1 < b := by grind
  have hsb : s.re ≤ b := by grind
  have hg : IntegrableOn g (positiveUnitFundamentalParamSet (K := K)) :=
    (integrableOn_centeredNonzeroFractionalShapeThetaMellinKernel_mk0 K J
      (by simp_all)).mono_set Set.inter_subset_left
  let q : mixedEmbedding.realSpace K → ℂ :=
    fun y ↦ logarithmicMellinWeight K s y /
      logarithmicMellinWeight K (b : ℂ) y
  have hq : Continuous q := by
    dsimp [q, logarithmicMellinWeight]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · simp
  have hfg : f = fun y ↦ q y * g y := by
    funext y
    dsimp [f, g, q, centeredNonzeroFractionalShapeThetaMellinKernel]
    field_simp [Complex.exp_ne_zero]
  have hfmeas :
      AEStronglyMeasurable f
        (volume.restrict (positiveUnitFundamentalParamSet (K := K))) := by
    rw [hfg]
    exact hq.aestronglyMeasurable.mul hg.aestronglyMeasurable
  apply Integrable.mono' hg.norm hfmeas
  filter_upwards [ae_restrict_mem measurableSet_positiveUnitFundamentalParamSet] with y hy
  exact norm_centeredNonzeroFractionalShapeThetaMellinKernel_mono K
    (I := I) (hy := le_of_lt hy.2) (hsb := hsb)

open Classical in
theorem differentiableAt_centeredPositiveClassThetaIntegral_mk0
    (J : (Ideal (𝓞 K))⁰) (s₀ : ℂ) :
    DifferentiableAt ℂ
      (centeredPositiveClassThetaIntegral K (FractionalIdeal.mk0 K J)) s₀ := by
  change DifferentiableAt ℂ
    (fun s ↦ ∫ y in positiveUnitFundamentalParamSet (K := K),
      centeredNonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K J) s y) s₀
  let I := FractionalIdeal.mk0 K J
  let P := positiveUnitFundamentalParamSet (K := K)
  let μ := volume.restrict P
  let F : ℂ → mixedEmbedding.realSpace K → ℂ :=
    fun s y ↦ centeredNonzeroFractionalShapeThetaMellinKernel K I s y
  let F' : ℂ → mixedEmbedding.realSpace K → ℂ :=
    fun s y ↦ centeredMellinRadialCoefficient K y * F s y
  let b : ℝ := s₀.re + 2
  let bound : mixedEmbedding.realSpace K → ℝ :=
    fun y ↦ ‖F (b : ℂ) y‖
  have hFint (s : ℂ) : Integrable (F s) μ :=
    integrableOn_positive_centeredNonzeroFractionalShapeThetaMellinKernel_mk0
      K J s
  have hFmeas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) μ := by
    filter_upwards with s
    exact (hFint s).aestronglyMeasurable
  have hcoeff :
      Continuous (centeredMellinRadialCoefficient K :
        mixedEmbedding.realSpace K → ℂ) := by
    unfold centeredMellinRadialCoefficient
    fun_prop
  have hF'meas : AEStronglyMeasurable (F' s₀) μ := by
    exact hcoeff.aestronglyMeasurable.mul (hFint s₀).aestronglyMeasurable
  have hbound : Integrable bound μ := (hFint (b : ℂ)).norm
  have hle :
      ∀ᵐ y ∂μ, ∀ s ∈ Metric.ball s₀ 1, ‖F' s y‖ ≤ bound y := by
    filter_upwards [ae_restrict_mem measurableSet_positiveUnitFundamentalParamSet] with y hy
    intro s hs
    have hnorm : ‖s - s₀‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq] using hs
    have hre : s.re - s₀.re ≤ ‖s - s₀‖ := by
      simpa only [sub_re] using Complex.re_le_norm (s - s₀)
    apply norm_centeredMellinRadialCoefficient_mul_kernel_le K
      (I := I) (hy := le_of_lt hy.2)
    grind
  have hdiff :
      ∀ᵐ y ∂μ, ∀ s ∈ Metric.ball s₀ 1,
        HasDerivAt (F · y) (F' s y) s := by
    filter_upwards with y
    intro s _
    exact hasDerivAt_centeredNonzeroFractionalShapeThetaMellinKernel K I s y
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := F) (F' := F') (bound := bound)
      (Metric.ball_mem_nhds s₀ one_pos) hFmeas (hFint s₀)
      hF'meas hle hbound hdiff
  simpa only [I, F, P, μ] using
    hmain.2.differentiableAt

open Classical in
theorem differentiable_centeredPositiveClassThetaIntegral_mk0
    (J : (Ideal (𝓞 K))⁰) :
    Differentiable ℂ
      (centeredPositiveClassThetaIntegral K (FractionalIdeal.mk0 K J)) :=
  fun s ↦ differentiableAt_centeredPositiveClassThetaIntegral_mk0 K J s

open Classical in
theorem differentiable_centeredPositiveClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (centeredPositiveClassThetaIntegral K I) := by
  rw [show centeredPositiveClassThetaIntegral K I =
      centeredPositiveClassThetaIntegral K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) by
    funext s
    exact centeredPositiveClassThetaIntegral_eq_numerator K I s]
  exact differentiable_centeredPositiveClassThetaIntegral_mk0 K
    (fractionalIdealNumerator K I)

open Classical in
/-- A pole cleared centered class theta integral used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCenteredClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (Module.finrank ℚ K : ℂ) * s * (1 - s) *
      (centeredPositiveClassThetaIntegral K I s +
        centeredPositiveClassThetaIntegral K
          (traceDualIdealUnit K I) (1 - s)) - 1

open Classical in
theorem differentiable_poleClearedCenteredClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (poleClearedCenteredClassThetaIntegral K I) := by
  have hI := differentiable_centeredPositiveClassThetaIntegral K I
  have hdual :=
    (differentiable_centeredPositiveClassThetaIntegral K
      (traceDualIdealUnit K I)).comp
      ((differentiable_const (c := (1 : ℂ))).sub differentiable_id)
  unfold poleClearedCenteredClassThetaIntegral
  fun_prop

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCenteredClassThetaIntegral_eq_mul_continued
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    poleClearedCenteredClassThetaIntegral K I s =
      (Module.finrank ℚ K : ℂ) * s * (1 - s) *
        centeredRadiallyContinuedClassThetaIntegral K I s := by
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  rw [poleClearedCenteredClassThetaIntegral,
    centeredRadiallyContinuedClassThetaIntegral,
    centeredClassThetaPoleTerm]
  grind

end NumberField.Odlyzko
