/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# Raw I1

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

theorem caccioppoli_timePartial_contDiff
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial ψ z) := by
  let F : (Vec3 × ℝ) → ℝ → ℝ := fun z s => ψ (z.1, s)
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Vec3 × ℝ) × ℝ => (q.1.1, q.2)) := by
    fun_prop
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
    convert hψ.comp hmap using 1
    funext q
    rfl
  have hderiv := hF.fderiv_apply
    (contDiff_snd (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
    (contDiff_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (c := (1 : ℝ)))
    (by simp)
  simpa only [F, timePartial, Function.uncurry] using hderiv

/-- Raw energy contribution from the time derivative and Laplacian of the heat cutoff. -/
def caccioppoliI1HeatCutoffRaw
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ ε r : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ℝ :=
  (∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z|).toReal

/-- Existence of an admissible time increment for the Caccioppoli heat cut-off,
matching the choice of `ε₀` at the start of the proof of Lemma `lem:caccioppoli`
(paper/ckn.tex §13): if a parabolic cylinder lies in the space-time domain
`spaceTimeSet Ω I` and `I` is open, then there is `0 < ε < r ^ 2` whose forward
time interval `Icc t₀ (t₀ + ε)` lies in `I`. The witness is a function of the
geometry alone, so no suitable-weak-solution data enters its construction. -/
theorem caccioppoli_admissible_heat_cutoff_exists
    {Ω : Set Vec3} {I : Set ℝ}
    {z₀ : ParabolicPoint} {ρ r : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hI : IsOpen I)
    (hsub : closure (parabolicCylinder z₀.1 z₀.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ^ 2 ∧
      Icc z₀.2 (z₀.2 + ε) ⊆ I := by
  have hzI : z₀.2 ∈ I := by
    apply (hsub ?_).2
    rw [closure_parabolicCylinder hρ]
    exact ⟨by simp [vec3EuclideanNorm_zero, hρ.le],
      ⟨by linarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
  obtain ⟨δ, hδ, hδI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hzI)
  refine ⟨min (r ^ 2 / 2) (δ / 2), ?_, ?_, ?_⟩
  · exact lt_min (by positivity) (by positivity)
  · exact lt_of_le_of_lt (min_le_left _ _)
      (by nlinarith only [sq_pos_of_pos hr])
  · intro t ht
    apply hδI
    rw [Metric.mem_ball]
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    calc
      t - z₀.2 ≤ min (r ^ 2 / 2) (δ / 2) := by linarith only [ht.2]
      _ ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith only [hδ]

private theorem caccioppoli_heat_cutoff_support_in_carrier
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (_ : ε < r ^ 2)
    (hsub : closure (parabolicCylinder (x₀) t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) :
    tsupport (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) ⊆
      spaceTimeSet Ω I := by
  have hsp : ∀ z ∈ tsupport (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε),
      z.1 ∈ Ω := by
    intro z hz
    have hclosed : Function.support (caccioppoliHeatCutoff
        x₀ t₀ ρ ε hρ hε) ⊆
        euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
          Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
      intro w hw
      have hmem := caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε hw
      refine ⟨?_, ?_⟩
      · exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity) |>.1 hmem.1 |>.le)
      · exact ⟨hmem.2.1.le, hmem.2.2.le⟩
    have hz' := closure_minimal hclosed
      (IsClosed.prod (isClosed_euclideanClosedBall x₀ (3 * ρ / 4)) isClosed_Icc) hz
    have hball : vec3EuclideanNorm (z.1 - x₀) ≤ ρ := by
      have hsmall' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by positivity)).1 hz'.1
      have hnorm : vec3EuclideanNorm (z.1 - x₀) =
          CKN.vecEuclideanNorm (z.1 - x₀) := by
        simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      have hsmall : vec3EuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := by
        rw [hnorm]
        exact hsmall'
      linarith only [hsmall, hρ]
    have hmem : (z.1, t₀) ∈ closure (parabolicCylinder x₀ t₀ ρ) := by
      rw [closure_parabolicCylinder hρ]
      exact ⟨hball, ⟨by linarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hsub hmem).1
  intro z hz
  refine ⟨hsp z hz, ?_⟩
  have hclosed : Function.support (caccioppoliHeatCutoff
      x₀ t₀ ρ ε hρ hε) ⊆
      euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
        Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
    intro w hw
    have hmem := caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε hw
    refine ⟨?_, ?_⟩
    · exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity) |>.1 hmem.1 |>.le)
    · exact ⟨hmem.2.1.le, hmem.2.2.le⟩
  have hz' := closure_minimal hclosed
    (IsClosed.prod (isClosed_euclideanClosedBall x₀ (3 * ρ / 4)) isClosed_Icc) hz
  rcases le_total z.2 t₀ with hle | hge
  · exact (hsub (by
      rw [closure_parabolicCylinder hρ]
      exact ⟨by
        have hsmall' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
          (by positivity)).1 hz'.1
        have hnorm : vec3EuclideanNorm (z.1 - x₀) =
            CKN.vecEuclideanNorm (z.1 - x₀) := by
          simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        have hsmall : vec3EuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := by
          rw [hnorm]
          exact hsmall'
        calc
          vec3EuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := hsmall
          _ ≤ ρ := by nlinarith only [hρ],
        ⟨by linarith only [hz'.2.1], hle⟩⟩)).2
  · exact hfuture ⟨hge, hz'.2.2⟩

theorem caccioppoli_heat_cutoff_testFunction
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) :
    backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r ∈
      spaceTimeTestFunction (V := ℝ) Ω I ∧
      (∀ z, 0 ≤ backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z) := by
  exact backwardHeat_cutoff_testFunction
    (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r hr
    (caccioppoli_heat_cutoff_smooth x₀ t₀ ρ ε hρ hε)
    (caccioppoli_heat_cutoff_hasCompactSupport x₀ t₀ ρ ε hρ hε)
    (caccioppoli_heat_cutoff_support_in_carrier hsol hρ hε hεr hsub hfuture)
    (caccioppoli_heat_cutoff_time_support_bound x₀ t₀ ρ ε r hρ hε hr hεr)
    (fun z => caccioppoli_heat_cutoff_nonneg x₀ t₀ ρ ε hρ hε z)

theorem caccioppoli_I1_heat_cutoff_raw_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) :
    caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
        6 * cutoffGradientConstant * 5000000) *
        (r ^ 2 / ρ ^ 5) * (ρ ^ 3 * alpha u ⟨x₀, t₀⟩ ρ ^ 2) := by
  let F : Vec3 × ℝ → ℝ :=
    fun z => backwardHeatCutoff
      (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z
  have htest := caccioppoli_heat_cutoff_testFunction hsol hρ hε hr hεr hsub hfuture
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    simpa only [F] using htest.1.1
  have htime := caccioppoli_timePartial_contDiff hF
  have hsecond (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialSecondPartial F i j z) := by
    exact spatialPartial_contDiff (spatialPartial_contDiff hF i) j
  have hlap : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ∑ i, spatialSecondPartial F i i z) := by
    apply ContDiff.sum
    intro i hi
    exact hsecond i i
  have hop : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ =>
        timePartial F z + ∑ i, spatialSecondPartial F i i z) :=
    htime.add hlap
  have hH : AEMeasurable
      (fun z : ParabolicPoint => ENNReal.ofReal
        |timePartial F z + ∑ i, spatialSecondPartial F i i z|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hcont : Continuous (fun z : Vec3 × ℝ => ENNReal.ofReal
        |timePartial F z + ∑ i, spatialSecondPartial F i i z|) :=
      ENNReal.continuous_ofReal.comp (hop.continuous.abs)
    exact hcont.aemeasurable
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hnorm : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hu
  have hU : AEMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hnorm' : AEStronglyMeasurable
        (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
        (volume.restrict (parabolicCylinder x₀ t₀ ρ)) :=
      hnorm.mono_measure (Measure.restrict_mono hcyl le_rfl)
    exact hnorm'.aemeasurable.pow_const (2 : ℝ)
  have hE := caccioppoli_I1_velocity_energy_bound hsol ⟨x₀, t₀⟩ hρ hsub
  have hCgrad : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ 0
    have hnorm' : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff x₀ hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    exact (not_lt_of_ge hnorm') (hbound.trans_lt hneg)
  have hCsecond : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
    exact (abs_nonneg (spatialSecondPartial
      (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) 0 0 (x₀, t₀))).trans
      (caccioppoli_heat_cutoff_second_spatial_partial_bound
        x₀ t₀ ρ ε hρ hε (x₀, t₀) 0 0)
  let C₁ : ℝ :=
    (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
        (8000000 * r ^ 2 / ρ ^ 3) +
      6 * (cutoffGradientConstant / ρ) *
        (5000000 * r ^ 2 / ρ ^ 4)
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    have hA : 0 ≤ 32 / ρ ^ 2 +
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      positivity
    have hB : 0 ≤ cutoffGradientConstant / ρ := div_nonneg hCgrad hρ.le
    positivity
  have hHC : (fun z : ParabolicPoint => ENNReal.ofReal
        |timePartial F z + ∑ i, spatialSecondPartial F i i z|) ≤ᵐ[
          volume.restrict (parabolicCylinder x₀ t₀ ρ)] (fun _ => ENNReal.ofReal C₁) := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with z hz
    have htime' := (mem_parabolicCylinder.mp hz).2.2
    have hz' : (z.1 - x₀, z.2 - t₀) ∈ parabolicCylinder 0 0 ρ := by
      rcases mem_parabolicCylinder.mp hz with ⟨hspace, hlo, hup⟩
      rw [parabolicCylinder]
      exact ⟨by simpa using hspace, ⟨by linarith only [hlo], by linarith only [hup]⟩⟩
    have hp := caccioppoli_I1_heat_cutoff_pointwise_on_cylinder
      hρ hε hr hscale hεr htime' hz'
    apply ENNReal.ofReal_le_ofReal
    change |timePartial (fun w : Vec3 × ℝ =>
      backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
      ∑ i, spatialSecondPartial (fun w : Vec3 × ℝ =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z| ≤ C₁
    change |timePartial (fun w : Vec3 × ℝ =>
      backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
      ∑ i, spatialSecondPartial (fun w : Vec3 × ℝ =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z| ≤
      (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        6 * (cutoffGradientConstant / ρ) *
          (5000000 * r ^ 2 / ρ ^ 4)
    exact hp
  have hprod : ENNReal.ofReal C₁ *
      ENNReal.ofReal (ρ ^ 3 * alpha u ⟨x₀, t₀⟩ ρ ^ 2) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound := caccioppoli_I1_toReal_lintegral_bound hU hH
    ENNReal.ofReal_ne_top hHC hE hprod
  have hright :
      (ENNReal.ofReal C₁ *
        ENNReal.ofReal (ρ ^ 3 * alpha u ⟨x₀, t₀⟩ ρ ^ 2)).toReal =
        C₁ * (ρ ^ 3 * alpha u ⟨x₀, t₀⟩ ρ ^ 2) := by
    rw [← ENNReal.ofReal_mul hC₁]
    exact ENNReal.toReal_ofReal (mul_nonneg hC₁ (by positivity))
  let K₁ : ℝ :=
    (32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
      6 * cutoffGradientConstant * 5000000
  have hscaleK : C₁ = K₁ * (r ^ 2 / ρ ^ 5) := by
    dsimp [C₁, K₁]
    field_simp [hρ.ne']
  change (∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z|).toReal ≤ _
  calc
    _ ≤ (ENNReal.ofReal C₁ *
        ENNReal.ofReal (ρ ^ 3 * alpha u ⟨x₀, t₀⟩ ρ ^ 2)).toReal := hbound
    _ = _ := by
      rw [hright, hscaleK]

theorem caccioppoli_I1_heat_cutoff_raw_normalized
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r C₂₅ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I)
    (hKbound :
      ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
        6 * cutoffGradientConstant * 5000000) ≤ C₂₅ ^ 2) :
    caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      (C₂₅ * (r / ρ) * alpha u ⟨x₀, t₀⟩ ρ) ^ 2 := by
  apply caccioppoli_I1_normalization hρ hr hKbound
  exact caccioppoli_I1_heat_cutoff_raw_bound hsol hρ hε hr hscale hεr
    hsub hfuture

end CKN
