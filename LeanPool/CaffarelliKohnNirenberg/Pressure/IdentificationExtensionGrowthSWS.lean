/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderForceTerms
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayPotentials
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpGrowth
public import LeanPool.CaffarelliKohnNirenberg.Setting.UTensor

/-!
# Identification Extension Growth SWS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN
open CKN.Foundation.Euclidean
private theorem lift_ball_memLp_growth_sws {g : Vec3 → ℝ} {B : Set Vec3}
    [IsFiniteMeasure (volume.restrict B)]
    (hB : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B))
    (hBsupport : tsupport g ⊆ B) :
    MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hsupport : Function.support g ⊆ B :=
    (subset_tsupport (f := g)).trans hBsupport
  have hgint : Integrable g volume := decomposition_full_of_on_sws
    (hB.integrable (by norm_num)) hBsupport
  exact memLp_volume_of_memLp_restrict_of_support
    hgint.aestronglyMeasurable hsupport hB
private theorem vec3_norm_le_sqrt_three_sws (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      _ ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) (by positivity)).mp hsq
private theorem vec3_norm_add_le_sws (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _
private theorem velocity_norm_memLp_six_on_ball
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x₀ : Vec3} {ρ t : ℝ} {Ω' : Set Vec3}
    (hρ : 0 < ρ) (hball : vec3Ball x₀ ρ ⊆ Ω')
    (hts : MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω'))
    (hDu : MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω'))
    (hgrad : ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x : Vec3 => u (x, t) i)
        (fun x => Du (x, t) i)) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 6
      (volume.restrict (vec3Ball x₀ ρ)) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ)
  have hμtop : μ Set.univ < ∞ := by simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball x₀ ρ) < ∞)
  haveI : IsFiniteMeasure μ := ⟨hμtop⟩
  have huB : MemLp (fun x : Vec3 => u (x, t)) 2 μ := by
    simpa [μ] using hts.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEMeasurable (fun x : Vec3 => u (x, t)) μ :=
    huB.aestronglyMeasurable.aemeasurable
  have humeasNorm : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) μ :=
    (continuous_vec3EuclideanNorm.measurable.comp_aemeasurable humeas).aestronglyMeasurable
  have hu2 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 μ := by
    apply huB.of_le_mul humeasNorm
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact vec3_norm_le_sqrt_three_sws (u (y, t))
  have hopen : IsOpen (euclideanBall x₀ ρ) := by
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < ρ ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hballEq : euclideanBall x₀ ρ = vec3Ball x₀ ρ := by
    ext x
    change (x ∈ euclideanBall x₀ ρ) ↔ vec3EuclideanNorm (x - x₀) < ρ
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ)
  have hballE : euclideanBall x₀ ρ ⊆ Ω' := by
    rw [hballEq]
    exact hball
  let hH1 : ∀ i : Fin 3, H1Function (euclideanBall x₀ ρ) := fun i =>
    { toFun := fun x => u (x, t) i
      grad := fun x => Du (x, t) i
      memL2 := (MemLp.eval hts i).mono_measure
        (Measure.restrict_mono_set volume hballE)
      gradMemL2 := fun j => (MemLp.eval (MemLp.eval hDu i) j).mono_measure
        (Measure.restrict_mono_set volume hballE)
      hasWeakGradient := (hgrad i).restrict hopen hballE }
  have hcomp : ∀ i : Fin 3, (hH1 i).toFun = fun x => u (x, t) i := by
    intro i
    simp [hH1]
  have hgrad' : ∀ i : Fin 3, (hH1 i).grad = fun x => Du (x, t) i := by
    intro i
    simp [hH1]
  have hbridge := vector_h1_sobolev_ball_integral hρ (fun x => u (x, t))
    (fun x i => Du (x, t) i) hH1 hcomp hgrad'
  have hW : MemLp (fun y : Vec3 => vec3EuclideanNorm (fun i : Fin 3 =>
      u (y, t) i - average μ (fun z => u (z, t) i))) 6 μ := by
    simpa [μ] using hbridge.1
  let cvec : Vec3 := fun j => average μ (fun z => u (z, t) j)
  let gw : Vec3 → ℝ := fun y => vec3EuclideanNorm (fun i : Fin 3 =>
    u (y, t) i - cvec i)
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, t))
  have hgw : MemLp gw 6 μ := by
    simpa [gw] using hW
  have hgu6 : MemLp gu 6 μ := by
    have hsum : MemLp (fun y => gw y + vec3EuclideanNorm cvec) 6 μ :=
      hgw.add (memLp_const _)
    apply hsum.of_le humeasNorm
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _),
      Real.norm_of_nonneg (add_nonneg (vec3EuclideanNorm_nonneg _)
        (vec3EuclideanNorm_nonneg _))]
    change vec3EuclideanNorm (u (y, t)) ≤
      vec3EuclideanNorm (fun i : Fin 3 => u (y, t) i - cvec i) +
        vec3EuclideanNorm cvec
    have hdecomp : u (y, t) = (fun i => u (y, t) i - cvec i) + cvec := by
      funext i
      dsimp [cvec]
      ring
    calc
      vec3EuclideanNorm (u (y, t)) = vec3EuclideanNorm
          ((fun i => u (y, t) i - cvec i) + cvec) := congrArg vec3EuclideanNorm hdecomp
      _ ≤ vec3EuclideanNorm (fun i => u (y, t) i - cvec i) +
          vec3EuclideanNorm cvec := vec3_norm_add_le_sws _ _
  exact hgu6
private theorem cutoff_laplacian_bound_sws {η : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) (hη : η = mollifiedBallCutoff x₀ hρ) :
    ∀ y, |spatialLaplacian η y| ≤
      (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
  intro y
  rw [hη, spatialLaplacian]
  calc
    |∑ i : Fin 3, mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| ≤
        ∑ i : Fin 3, |mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
      gcongr with i hi
      exact pressure_cutoff_mixedSecond_bound x₀ hρ y i i
    _ = (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
theorem pressureSecondExtension_residual_growth_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ R : ℝ, 0 < R →
          MemLp (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y => u (y, t) j)) p f s x -
            pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
              (fun i j x => mollifiedBallCutoff z.1 hρ x *
                pressureUTensor u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y => u (y, t) j)) (x, s) i j) x)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
        (∀ R : ℝ, 0 < R →
          lpNorm (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y => u (y, t) j)) p f s x -
            pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
              (fun i j x => mollifiedBallCutoff z.1 hρ x *
                pressureUTensor u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y => u (y, t) j)) (x, s) i j) x)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R)) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j => average (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  let R₀ : ℝ := vec3EuclideanNorm z.1 + ρ
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith only [vec3EuclideanNorm_nonneg z.1, hρ]
  have hB0 : vec3Ball z.1 ρ ⊆ closedBall (0 : Vec3) R₀ := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    have hy' : vec3EuclideanNorm (y - z.1) < ρ := (mem_vec3Ball).1 hy
    have htri : vec3EuclideanNorm y ≤ vec3EuclideanNorm (y - z.1) + vec3EuclideanNorm z.1 := by
      calc
        vec3EuclideanNorm y =
            vec3EuclideanNorm ((y - z.1) + z.1) := by congr 1; abel
        _ ≤ vec3EuclideanNorm (y - z.1) + vec3EuclideanNorm z.1 :=
          vec3_norm_add_le_sws _ _
    have hyNorm : ‖y‖ ≤ vec3EuclideanNorm y := by
      rw [Pi.norm_def]
      have hnn : Finset.univ.sup (fun i => ‖y i‖₊) ≤
          ⟨vec3EuclideanNorm y, vec3EuclideanNorm_nonneg y⟩ := by
        apply Finset.sup_le
        intro i hi
        have hi' : |y i| ≤ vec3EuclideanNorm y := by
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using abs_apply_le_vecEuclideanNorm y i
        exact_mod_cast hi'
      exact_mod_cast hnn
    linarith only [hy', htri, hyNorm]
  have hbox := pressure_box_geometry hsol hρ hsub
  obtain ⟨Ω', J, hbox', hball, htime⟩ := hbox
  have hslice := slice_memLp_ae_of_sws hsol hbox'
  have hgradJ : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x : Vec3 => u (x, s) i)
        (fun x => Du (x, s) i) := by
    obtain ⟨_, _, _, _, _, _, _, _, hgrad⟩ := hsol.2.2.2.2.2.1 Ω' J hbox'
    filter_upwards [hgrad 0, hgrad 1, hgrad 2] with s h0 h1 h2
    intro i
    fin_cases i <;> assumption
  have hsliceT := ae_restrict_of_ae_restrict_of_subset htime hslice
  have hgradT := ae_restrict_of_ae_restrict_of_subset htime hgradJ
  have hforce := pressure_force_memLp_and_lpNorm_growth_ae_of_sws hsol hρ hsub
  have hpT := sws_pressure_memLp_slice_ae hsol hρ hsub
  filter_upwards [hsliceT, hgradT, hforce, hpT] with s hs hg hJ hp
  have hgu6 := velocity_norm_memLp_six_on_ball hρ hball hs.1 hs.2 (hg ·)
  let μ : Measure Vec3 := volume.restrict (vec3Ball z.1 ρ)
  have hμtop : μ Set.univ < ∞ := by simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball z.1 ρ) < ∞)
  haveI : IsFiniteMeasure μ := ⟨hμtop⟩
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, s))
  have humeas : AEStronglyMeasurable gu μ := by
    exact (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hs.1.aestronglyMeasurable).mono_measure
      (Measure.restrict_mono_set volume hball)
  have hc6 : MemLp (fun _ : Vec3 => vec3EuclideanNorm (c s)) 6 μ := memLp_const _
  have hsum6 : MemLp (fun y => gu y + vec3EuclideanNorm (c s)) 6 μ :=
    hgu6.add hc6
  have hgu6' : MemLp gu (ENNReal.ofReal (6 : ℝ)) μ := by
    simpa using hgu6
  have hsum6' : MemLp (fun y => gu y + vec3EuclideanNorm (c s)) (ENNReal.ofReal (6 : ℝ)) μ := by
    simpa using hsum6
  haveI : (ENNReal.ofReal (6 : ℝ)).HolderTriple (ENNReal.ofReal (6 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) := by
    have h : (6 : ℝ).HolderTriple 6 3 := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have hmajor : MemLp (fun y => gu y * (gu y + vec3EuclideanNorm (c s)))
      (ENNReal.ofReal (3 : ℝ)) μ := hgu6'.mul hsum6'
  have huMeas : AEMeasurable (fun x : Vec3 => u (x, s)) μ := by
    exact (hs.1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hball)).aemeasurable
  have hUmeas (i j : Fin 3) : AEStronglyMeasurable (fun y => pressureUTensor u c (y, s) i j) μ := by
    let F : Vec3 → ℝ := fun v => -v i * (v j - c s j)
    have hF : Continuous F := by
      dsimp [F]
      fun_prop
    exact (hF.measurable.comp_aemeasurable huMeas).aestronglyMeasurable
  have hU32 (i j : Fin 3) : MemLp (fun y => pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    have hU3 : MemLp (fun y => pressureUTensor u c (y, s) i j)
        (ENNReal.ofReal (3 : ℝ)) μ := by
      apply hmajor.of_le (hUmeas i j)
      filter_upwards [] with y
      have hui : |u (y, s) i| ≤ gu y := by
        simpa [gu, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
          abs_apply_le_vecEuclideanNorm (u (y, s)) i
      have huj : |u (y, s) j| ≤ gu y := by
        simpa [gu, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
          abs_apply_le_vecEuclideanNorm (u (y, s)) j
      have hcj : |c s j| ≤ vec3EuclideanNorm (c s) := by
        simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
          abs_apply_le_vecEuclideanNorm (c s) j
      calc
        ‖pressureUTensor u c (y, s) i j‖ =
            |-(u (y, s) i * u (y, s) j) + c s j * u (y, s) i| := by
          change ‖-u (y, s) i * (u (y, s) j - c s j)‖ = _
          rw [Real.norm_eq_abs]
          congr 1
          ring
        _ ≤ |u (y, s) i * u (y, s) j| + |c s j * u (y, s) i| := by
          calc
            _ ≤ |-(u (y, s) i * u (y, s) j)| + |c s j * u (y, s) i| :=
              abs_add_le _ _
            _ = |u (y, s) i * u (y, s) j| + |c s j * u (y, s) i| := by
              rw [abs_neg]
        _ ≤ gu y * (gu y + vec3EuclideanNorm (c s)) := by
          rw [abs_mul, abs_mul]
          nlinarith only [hui, huj, hcj, abs_nonneg (u (y, s) i),
            abs_nonneg (u (y, s) j), abs_nonneg (c s j)]
        _ = ‖gu y * (gu y + vec3EuclideanNorm (c s))‖ := by
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (vec3EuclideanNorm_nonneg _),
            abs_of_nonneg (add_nonneg (vec3EuclideanNorm_nonneg _)
              (vec3EuclideanNorm_nonneg _))]
    exact hU3.mono_exponent (by norm_num)
  have hηc : HasCompactSupport η := by
    simpa [η] using mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using mollifiedBallCutoff_smooth z.1 hρ
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ := by
    simpa [η] using pressure_cutoff_support_subset_ball z.1 hρ
  have hηbound : ∀ y, |η y| ≤ 1 := by
    intro y
    exact abs_le.mpr ⟨by linarith only [mollifiedBallCutoff_nonneg z.1 hρ y],
      by simpa [η] using mollifiedBallCutoff_le_one z.1 hρ y⟩
  have hηboundAE : ∀ᵐ y ∂μ, ‖η y‖ ≤ (1 : ℝ) := by
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs] using hηbound y
  have hηmeas : AEStronglyMeasurable η μ :=
    hηsmooth.continuous.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hball)
  have hC₁ : 0 ≤ cutoffGradientConstant := by
    have hx := pressure_cutoff_spatialDeriv_bound z.1 hρ z.1 (0 : Fin 3)
    have hx' : 0 ≤ cutoffGradientConstant / ρ := (abs_nonneg _).trans hx
    rcases (div_nonneg_iff.mp hx') with h | h
    · exact h.1
    · exfalso
      linarith only [hρ, h.2]
  have hC₂ : 0 ≤ cutoffSecondDerivativeConstant := by
    have hx := pressure_cutoff_mixedSecond_bound z.1 hρ z.1 (0 : Fin 3) 0
    have hx' : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := (abs_nonneg _).trans hx
    rcases (div_nonneg_iff.mp hx') with h | h
    · exact h.1
    · exfalso
      linarith only [sq_pos_of_pos hρ, h.2]
  have hsupp (g : Vec3 → ℝ) (ht : tsupport g ⊆ vec3Ball z.1 ρ) :
      ∀ y ∉ closedBall (0 : Vec3) R₀, g y = 0 := by
    intro y hy
    have hyB : y ∉ vec3Ball z.1 ρ := fun hyB => hy (hB0 hyB)
    exact image_eq_zero_of_notMem_tsupport (fun hgy => hyB (ht hgy))
  have hηpB := pressure_cutoff_pressure_memLp_slice hp hηmeas hηboundAE
  have hηpsupp : tsupport (fun y => η y * p (y, s)) ⊆ vec3Ball z.1 ρ :=
    (tsupport_mul_subset_left (f := η) (g := fun y => p (y, s))).trans hηsupport
  have hηp : MemLp (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    lift_ball_memLp_growth_sws hηpB hηpsupp
  have hηpBound : ∀ r : ℝ, 0 < r → lpNorm (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      lpNorm (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume * (1 + r) := by
    intro r hr
    exact lpNorm_euclideanBall_le_of_memLp_volume hηp hr
  have hsrc (g : Vec3 → ℝ) (hgb : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) μ)
      (hgt : tsupport g ⊆ vec3Ball z.1 ρ) :
      MemLp g (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    have hgg := lift_ball_memLp_growth_sws hgb hgt
    exact memLp_six_fifths_of_memLp_ofReal (by norm_num) hgg (hsupp g hgt)
  have hsrcη (k : ℝ) (hk : 0 ≤ k) (g : Vec3 → ℝ)
      (hgb : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) μ)
      (hgm : AEStronglyMeasurable g μ)
      (hbound : ∀ᵐ y ∂μ, |η y| ≤ k) :
      MemLp (fun y => η y * g y) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply hgb.of_le_mul
      ((hηsmooth.continuous.aestronglyMeasurable.mul hgm))
    filter_upwards [hbound] with y hy
    change |η y * g y| ≤ k * ‖g y‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hGμ (i j : Fin 3) : MemLp (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    exact hsrcη 1 (by norm_num) (fun y => pressureUTensor u c (y, s) i j)
      (hU32 i j) (hUmeas i j)
      (Eventually.of_forall hηbound)
  have hG (i j : Fin 3) : MemLp (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    exact lift_ball_memLp_growth_sws (hGμ i j)
      ((tsupport_mul_subset_left (f := η)
        (g := fun y => pressureUTensor u c (y, s) i j)).trans hηsupport)
  have hGc : ∀ i j, HasCompactSupport
      (fun y => η y * pressureUTensor u c (y, s) i j) := by
    intro i j
    exact hηc.mul_right
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) := contDiff_spatialDeriv_smooth hηsmooth i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) := contDiff_mixedSecond_smooth hηsmooth i j
  have hηlap : HasCompactSupport (spatialLaplacian η) :=
    decomposition_laplacian_hasCompactSupport_sws hηc
  have hηlapB : tsupport (spatialLaplacian η) ⊆ vec3Ball z.1 ρ := by
    change tsupport (fun x => ∑ i : Fin 3, spatialDeriv (spatialDeriv η i) i x) ⊆ vec3Ball z.1 ρ
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηsupport)
  have hηdBound (i : Fin 3) : ∀ᵐ y ∂μ, |spatialDeriv η i y| ≤ cutoffGradientConstant / ρ := by
    filter_upwards [] with y
    simpa [η] using pressure_cutoff_spatialDeriv_bound z.1 hρ y i
  have hηmBound (i j : Fin 3) : ∀ᵐ y ∂μ, |mixedSecond η i j y| ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
    filter_upwards [] with y
    simpa [η] using pressure_cutoff_mixedSecond_bound z.1 hρ y i j
  have hηlapBound : ∀ᵐ y ∂μ,
      |spatialLaplacian η y| ≤ (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
    filter_upwards [] with y
    exact cutoff_laplacian_bound_sws (x₀ := z.1) hρ (by rfl) y
  have hPmeas : AEStronglyMeasurable (fun y => p (y, s)) μ := hp.aestronglyMeasurable
  have hsource2 (i j : Fin 3) : MemLp (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply (hU32 i j).of_le_mul
      ((hηm i j).continuous.aestronglyMeasurable.mul (hUmeas i j))
    filter_upwards [hηmBound i j] with y hy
    change |mixedSecond η i j y * pressureUTensor u c (y, s) i j| ≤
      (cutoffSecondDerivativeConstant / ρ ^ 2) *
        ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hsource3 (i j : Fin 3) : MemLp (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply (hU32 i j).of_le_mul
      ((hUmeas i j).mul (hηd i).continuous.aestronglyMeasurable)
    filter_upwards [hηdBound i] with y hy
    change |pressureUTensor u c (y, s) i j * spatialDeriv η i y| ≤
      (cutoffGradientConstant / ρ) *
        ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hsource4 (i j : Fin 3) : MemLp (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply (hU32 i j).of_le_mul
      ((hUmeas i j).mul (hηd j).continuous.aestronglyMeasurable)
    filter_upwards [hηdBound j] with y hy
    change |pressureUTensor u c (y, s) i j * spatialDeriv η j y| ≤
      (cutoffGradientConstant / ρ) *
        ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans_eq (by ring)
  have hsource5 : MemLp (fun y => p (y, s) * spatialLaplacian η y) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply hp.of_le_mul
      (hPmeas.mul (contDiff_spatialLaplacian_smooth hηsmooth).continuous.aestronglyMeasurable)
    filter_upwards [hηlapBound] with y hy
    change |p (y, s) * spatialLaplacian η y| ≤
      (3 * cutoffSecondDerivativeConstant / ρ ^ 2) * ‖p (y, s)‖
    rw [abs_mul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hsource6 (j : Fin 3) : MemLp (fun y => spatialDeriv η j y * p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply hp.of_le_mul
      ((hηd j).continuous.aestronglyMeasurable.mul hPmeas)
    filter_upwards [hηdBound j] with y hy
    change |spatialDeriv η j y * p (y, s)| ≤
      (cutoffGradientConstant / ρ) * ‖p (y, s)‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  let g2 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    mixedSecond η i j y * pressureUTensor u c (y, s) i j
  let g3 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    pressureUTensor u c (y, s) i j * spatialDeriv η i y
  let g4 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    pressureUTensor u c (y, s) i j * spatialDeriv η j y
  let g5 : Vec3 → ℝ := fun y => p (y, s) * spatialLaplacian η y
  let g6 : Fin 3 → Vec3 → ℝ := fun j y => spatialDeriv η j y * p (y, s)
  have hg2 (i j : Fin 3) : MemLp (g2 i j) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    apply hsrc (g2 i j) (hsource2 i j)
      ((tsupport_mul_subset_left (f := mixedSecond η i j)
        (g := fun y => pressureUTensor u c (y, s) i j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)))
  have hg3 (i j : Fin 3) : MemLp (g3 i j) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    apply hsrc (g3 i j) (hsource3 i j)
      ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η i)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηsupport))
  have hg4 (i j : Fin 3) : MemLp (g4 i j) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    apply hsrc (g4 i j) (hsource4 i j)
      ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport))
  have hg5 : MemLp g5 (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    apply hsrc g5 hsource5 ((tsupport_mul_subset_right
      (f := fun y => p (y, s)) (g := spatialLaplacian η)).trans hηlapB)
  have hg6 (j : Fin 3) : MemLp (g6 j) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    apply hsrc (g6 j) (hsource6 j)
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => p (y, s))).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport))
  have hp2ij (i j : Fin 3) :=
    pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp
      (G := g2 i j) hR₀ (by norm_num) (hg2 i j) (hsupp _
        ((tsupport_mul_subset_left (f := mixedSecond η i j)
          (g := fun y => pressureUTensor u c (y, s) i j)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
              ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport))))
  have hp3ij (i j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp j hR₀
      (by norm_num) (hg3 i j) (hsupp _
        ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η i)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηsupport)))
  have hp4ij (i j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp i hR₀
      (by norm_num) (hg4 i j) (hsupp _
        ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η j)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)))
  have hp5 := pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp
    (G := g5) hR₀ (by norm_num) hg5 (hsupp _
      ((tsupport_mul_subset_right (f := fun y => p (y, s))
        (g := spatialLaplacian η)).trans hηlapB))
  have hp6 (j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp j hR₀
      (by norm_num) (hg6 j) (hsupp _
        ((tsupport_mul_subset_left (f := spatialDeriv η j)
          (g := fun y => p (y, s))).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)))
  let f2 : Fin 3 × Fin 3 → Vec3 → ℝ := fun ij =>
    pressureNewtonianPotential (g2 ij.1 ij.2)
  let f3 : Fin 3 × Fin 3 → Vec3 → ℝ := fun ij =>
    pressureNewtonianDerivativePotential ij.2 (g3 ij.1 ij.2)
  let f4 : Fin 3 × Fin 3 → Vec3 → ℝ := fun ij =>
    pressureNewtonianDerivativePotential ij.1 (g4 ij.1 ij.2)
  let C2 : Fin 3 × Fin 3 → ℝ := fun ij =>
    newtonianPotentialGrowthConstant (g2 ij.1 ij.2) R₀
  let C3 : Fin 3 × Fin 3 → ℝ := fun ij =>
    newtonianDerivativePotentialGrowthConstant ij.2 (g3 ij.1 ij.2) R₀
  let C4 : Fin 3 × Fin 3 → ℝ := fun ij =>
    newtonianDerivativePotentialGrowthConstant ij.1 (g4 ij.1 ij.2) R₀
  have hf2 : pressureP2 η u c s = fun x => ∑ ij : Fin 3 × Fin 3, f2 ij x := by
    funext x
    simp only [pressureP2, f2, g2]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hf3 : pressureP3 η u c s = fun x => ∑ ij : Fin 3 × Fin 3, f3 ij x := by
    funext x
    simp only [pressureP3, f3, g3]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hf4 : pressureP4 η u c s = fun x => ∑ ij : Fin 3 × Fin 3, f4 ij x := by
    funext x
    simp only [pressureP4, f4, g4]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have h2mem : ∀ r : ℝ, 0 < r → MemLp (pressureP2 η u c s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    have h := memLp_finsetSum (p := ENNReal.ofReal (3 / 2 : ℝ))
      (Finset.univ : Finset (Fin 3 × Fin 3)) (fun ij _ => (hp2ij ij.1 ij.2).1 r hr)
    rw [hf2]
    exact h
  have h2bound : ∀ r : ℝ, 0 < r → lpNorm (pressureP2 η u c s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      (∑ ij : Fin 3 × Fin 3, C2 ij) * (1 + r) := by
    intro r hr
    have h := lpNorm_euclideanBall_growth_sum (s := Finset.univ) (f := f2) (C := C2)
      (fun ij _ r hr => (hp2ij ij.1 ij.2).1 r hr)
      (fun ij _ r hr => (hp2ij ij.1 ij.2).2 r hr) hr
    rw [hf2]
    exact h
  have h3mem : ∀ r : ℝ, 0 < r → MemLp (pressureP3 η u c s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    have h := memLp_finsetSum (p := ENNReal.ofReal (3 / 2 : ℝ))
      (Finset.univ : Finset (Fin 3 × Fin 3)) (fun ij _ => (hp3ij ij.1 ij.2).1 r hr)
    rw [hf3]
    exact h
  have h3bound : ∀ r : ℝ, 0 < r → lpNorm (pressureP3 η u c s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      (∑ ij : Fin 3 × Fin 3, C3 ij) * (1 + r) := by
    intro r hr
    have h := lpNorm_euclideanBall_growth_sum (s := Finset.univ) (f := f3) (C := C3)
      (fun ij _ r hr => (hp3ij ij.1 ij.2).1 r hr)
      (fun ij _ r hr => (hp3ij ij.1 ij.2).2 r hr) hr
    rw [hf3]
    exact h
  have h4mem : ∀ r : ℝ, 0 < r → MemLp (pressureP4 η u c s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    have h := memLp_finsetSum (p := ENNReal.ofReal (3 / 2 : ℝ))
      (Finset.univ : Finset (Fin 3 × Fin 3)) (fun ij _ => (hp4ij ij.1 ij.2).1 r hr)
    rw [hf4]
    exact h
  have h4bound : ∀ r : ℝ, 0 < r → lpNorm (pressureP4 η u c s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      (∑ ij : Fin 3 × Fin 3, C4 ij) * (1 + r) := by
    intro r hr
    have h := lpNorm_euclideanBall_growth_sum (s := Finset.univ) (f := f4) (C := C4)
      (fun ij _ r hr => (hp4ij ij.1 ij.2).1 r hr)
      (fun ij _ r hr => (hp4ij ij.1 ij.2).2 r hr) hr
    rw [hf4]
    exact h
  have hp5mem : ∀ r : ℝ, 0 < r → MemLp (pressureP5 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    change MemLp (fun x => -pressureNewtonianPotential g5 x)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))
    change MemLp (-(pressureNewtonianPotential g5))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))
    exact (hp5.1 r hr).neg
  have hp5bound : ∀ r : ℝ, 0 < r → lpNorm (pressureP5 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      newtonianPotentialGrowthConstant g5 R₀ * (1 + r) := by
    intro r hr
    change lpNorm (-(pressureNewtonianPotential g5))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ _
    simpa using hp5.2 r hr
  have hp6mem : ∀ r : ℝ, 0 < r → MemLp (pressureP6 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    have h := memLp_finsetSum (p := ENNReal.ofReal (3 / 2 : ℝ))
      (Finset.univ : Finset (Fin 3)) (fun j _ => (hp6 j).1 r hr)
    change MemLp ((-2 : ℝ) • (fun x => ∑ j : Fin 3,
      pressureNewtonianDerivativePotential j (g6 j) x))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))
    exact h.const_smul (-2 : ℝ)
  have hp6bound : ∀ r : ℝ, 0 < r → lpNorm (pressureP6 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      (∑ j : Fin 3, 2 * newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) * (1 + r) := by
    intro r hr
    have h := lpNorm_euclideanBall_growth_sum (s := Finset.univ) (f := fun j =>
        pressureNewtonianDerivativePotential j (g6 j))
      (C := fun j => newtonianDerivativePotentialGrowthConstant j (g6 j) R₀)
      (fun j _ r hr => (hp6 j).1 r hr) (fun j _ r hr => (hp6 j).2 r hr) hr
    let S : Vec3 → ℝ := fun x => ∑ j : Fin 3,
      pressureNewtonianDerivativePotential j (g6 j) x
    have hS : lpNorm S (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (∑ j : Fin 3, newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) *
          (1 + r) := by
      change lpNorm (∑ j : Fin 3, pressureNewtonianDerivativePotential j (g6 j))
        (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ _
      exact h
    calc
      lpNorm (pressureP6 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) =
          2 * lpNorm S (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) := by
        rw [show pressureP6 η p s = fun x => (-2 : ℝ) * S x by
          funext x; simp [pressureP6, g6, S]]
        rw [show (fun x => (-2 : ℝ) * S x) = (-2 : ℝ) • S by
          funext x; simp [smul_eq_mul]]
        rw [lpNorm_const_smul]
        norm_num
      _ ≤ 2 * ((∑ j : Fin 3,
          newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) * (1 + r)) :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = (∑ j : Fin 3, 2 *
          newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) * (1 + r) := by
        rw [← Finset.mul_sum]
        ring
  let H : Vec3 → ℝ := (((pressureP2 η u c s + pressureP3 η u c s) + pressureP4 η u c s) + pressureP5 η p s) + pressureP6 η p s
  let C_H : ℝ := (∑ ij : Fin 3 × Fin 3, C2 ij) +
    (∑ ij : Fin 3 × Fin 3, C3 ij) + (∑ ij : Fin 3 × Fin 3, C4 ij) +
    newtonianPotentialGrowthConstant g5 R₀ +
    (∑ j : Fin 3, 2 * newtonianDerivativePotentialGrowthConstant j (g6 j) R₀)
  have hHmem : ∀ r : ℝ, 0 < r → MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    exact (((((h2mem r hr).add (h3mem r hr)).add (h4mem r hr)).add
      (hp5mem r hr)).add (hp6mem r hr))
  have hHbound : ∀ r : ℝ, 0 < r → lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C_H * (1 + r) := by
    intro r hr
    dsimp [H, C_H]
    have hn23 : lpNorm (pressureP2 η u c s + pressureP3 η u c s)
        (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        lpNorm (pressureP2 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) +
        lpNorm (pressureP3 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) := by
      exact lpNorm_add_le (h2mem r hr) (g := pressureP3 η u c s) (by norm_num)
    have hn234 : lpNorm ((pressureP2 η u c s + pressureP3 η u c s) +
        pressureP4 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        lpNorm (pressureP2 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) +
        lpNorm (pressureP3 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) +
        lpNorm (pressureP4 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) := by
      calc
        _ ≤ lpNorm (pressureP2 η u c s + pressureP3 η u c s)
            (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) r)) +
            lpNorm (pressureP4 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) r)) := by
          exact lpNorm_add_le ((h2mem r hr).add (h3mem r hr))
            (g := pressureP4 η u c s) (by norm_num)
        _ ≤ _ := by linarith only [hn23]
    have hn2345 : lpNorm (((pressureP2 η u c s + pressureP3 η u c s) +
        pressureP4 η u c s) + pressureP5 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        lpNorm (pressureP2 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) +
        lpNorm (pressureP3 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) +
        lpNorm (pressureP4 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) +
        lpNorm (pressureP5 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) := by
      calc
        _ ≤ lpNorm ((pressureP2 η u c s + pressureP3 η u c s) +
            pressureP4 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) r)) +
            lpNorm (pressureP5 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) r)) := by
          exact lpNorm_add_le ((h2mem r hr).add (h3mem r hr) |>.add (h4mem r hr))
            (g := pressureP5 η p s) (by norm_num)
        _ ≤ _ := by linarith only [hn234]
    calc
      _ ≤ lpNorm (fun x => pressureP2 η u c s x + pressureP3 η u c s x +
          pressureP4 η u c s x + pressureP5 η p s x)
          (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm (pressureP6 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) := by
        exact lpNorm_add_le ((h2mem r hr).add (h3mem r hr) |>.add (h4mem r hr) |>.add
          (hp5mem r hr)) (g := pressureP6 η p s) (by norm_num)
      _ ≤ lpNorm (pressureP2 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm (pressureP3 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm (pressureP4 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm (pressureP5 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm (pressureP6 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) := by
        exact add_le_add hn2345 (le_refl _)
      _ ≤ (∑ ij : Fin 3 × Fin 3, C2 ij) * (1 + r) +
          (∑ ij : Fin 3 × Fin 3, C3 ij) * (1 + r) +
          (∑ ij : Fin 3 × Fin 3, C4 ij) * (1 + r) +
          newtonianPotentialGrowthConstant g5 R₀ * (1 + r) +
          (∑ j : Fin 3, 2 * newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) *
            (1 + r) := by
        have hconst2345 :
            lpNorm (pressureP2 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall (0 : Vec3) r)) +
              lpNorm (pressureP3 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall (0 : Vec3) r)) +
              lpNorm (pressureP4 η u c s) (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall (0 : Vec3) r)) +
              lpNorm (pressureP5 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
            (∑ ij : Fin 3 × Fin 3, C2 ij) * (1 + r) +
              (∑ ij : Fin 3 × Fin 3, C3 ij) * (1 + r) +
              (∑ ij : Fin 3 × Fin 3, C4 ij) * (1 + r) +
              newtonianPotentialGrowthConstant g5 R₀ * (1 + r) := by
          exact add_le_add (add_le_add (add_le_add
            (h2bound r hr) (h3bound r hr)) (h4bound r hr)) (hp5bound r hr)
        exact add_le_add hconst2345 (hp6bound r hr)
      _ = C_H * (1 + r) := by ring
  have hC_H : 0 ≤ C_H := by
    dsimp [C_H, C2, C3, C4]
    apply add_nonneg
    · apply add_nonneg
      · apply add_nonneg
        · apply add_nonneg
          · exact Finset.sum_nonneg (fun ij _ =>
              newtonianPotentialGrowthConstant_nonneg _ _)
          · exact Finset.sum_nonneg (fun ij _ =>
              newtonianDerivativePotentialGrowthConstant_nonneg _ hR₀ _)
        · exact Finset.sum_nonneg (fun ij _ =>
            newtonianDerivativePotentialGrowthConstant_nonneg _ hR₀ _)
      · exact newtonianPotentialGrowthConstant_nonneg _ _
    · apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (by norm_num)
        (newtonianDerivativePotentialGrowthConstant_nonneg j hR₀ _)
  obtain ⟨hJmem, hJnonneg, hJbound⟩ := hJ
  have hT := pressureSecondExtension_memLp rieszSecondL2Input rieszSecondL2_weak_type hG
  have hres := pressureSecondExtension_residual_growth_of_decomposition
    (p₁ := pressureP1 η u c p f s)
    (P := fun y => η y * p (y, s))
    (H := H)
    (J := pressureP7 η f s + pressureP8 η f s)
    (T := pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
      (fun i j y => η y * pressureUTensor u c (y, s) i j))
    (hdecomp := by
      funext x
      simp only [pressureP1, H, Pi.sub_apply, Pi.add_apply]
      ring)
    (C₀ := lpNorm (fun y => η y * p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (C_H := C_H) (C_J :=
      pressureP7GrowthConstant η f s R₀ + pressureP8GrowthConstant η f s R₀)
    (C_T := lpNorm (pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
      (fun i j y => η y * pressureUTensor u c (y, s) i j))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (by intro r hr; exact hηp.restrict _) hηpBound hHmem hHbound hJmem hJbound
      (by intro r hr; exact memLp_euclideanBall_of_memLp_volume hT r)
      (by intro r hr; exact lpNorm_euclideanBall_le_of_memLp_volume hT hr)
  let C : ℝ := lpNorm (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume + C_H +
      (pressureP7GrowthConstant η f s R₀ + pressureP8GrowthConstant η f s R₀) +
      lpNorm (pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
        (fun i j y => η y * pressureUTensor u c (y, s) i j))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume
  refine ⟨C, ?_, ?_, ?_⟩
  · dsimp [C]
    exact add_nonneg (add_nonneg (add_nonneg lpNorm_nonneg hC_H) hJnonneg) lpNorm_nonneg
  · intro R hR
    simpa [η, c, R₀, H, C] using (hres R hR).1
  · intro R hR
    simpa [η, c, R₀, H, C] using (hres R hR).2
end CKN
