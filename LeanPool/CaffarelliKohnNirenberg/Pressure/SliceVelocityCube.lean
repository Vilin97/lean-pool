/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.MemLpThreeHalvesLift
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore
public import LeanPool.CaffarelliKohnNirenberg.Pressure.UTensorNormFactor
public import LeanPool.CaffarelliKohnNirenberg.Setting.UTensor

/-!
# Cubic integrability of velocity slices

The local weak-gradient data of a suitable weak solution give spatial `L^6`
regularity on almost every ball slice, hence `L^3` integrability.  The cut-off
velocity tensor then supplies compactly supported `L^{3/2}` sources for the
unconditional Calderón--Zygmund estimate.  The nine-entry source bound retains
its dimension factor by packaging it into the source energy.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem vec3_norm_add_le_slice_velocity (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem vec3_norm_le_sqrt_three_slice_velocity (v : Vec3) :
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

/-- A local `H¹` velocity slice has Euclidean norm in `L³` on an interior ball.
The proof obtains `L⁶` from the same-ball weak Sobolev estimate and lowers the
exponent on the finite-measure ball. -/
theorem velocity_norm_memLp_three_on_ball_of_slices
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x₀ : Vec3} {ρ t : ℝ} {Ω' : Set Vec3}
    (hρ : 0 < ρ) (hball : vec3Ball x₀ ρ ⊆ Ω')
    (hts : MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω'))
    (hDu : MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω'))
    (hgrad : ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x : Vec3 => u (x, t) i)
        (fun x => Du (x, t) i)) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ)) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ)
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball x₀ ρ) < ∞)
  have : IsFiniteMeasure μ := ⟨hμtop⟩
  have huB : MemLp (fun x : Vec3 => u (x, t)) 2 μ := by
    simpa [μ] using hts.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEMeasurable (fun x : Vec3 => u (x, t)) μ :=
    huB.aestronglyMeasurable.aemeasurable
  have humeasNorm : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) μ :=
    (continuous_vec3EuclideanNorm.measurable.comp_aemeasurable humeas).aestronglyMeasurable
  have hu2 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 μ := by
    apply huB.of_le_mul humeasNorm
    on_goal 1 => filter_upwards [] with y
    on_goal 1 => rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact vec3_norm_le_sqrt_three_slice_velocity (u (y, t))
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
      vec3EuclideanNorm (u (y, t)) =
          vec3EuclideanNorm ((fun i => u (y, t) i - cvec i) + cvec) :=
        congrArg vec3EuclideanNorm hdecomp
      _ ≤ vec3EuclideanNorm (fun i => u (y, t) i - cvec i) +
          vec3EuclideanNorm cvec := vec3_norm_add_le_slice_velocity _ _
  have hgu6' : MemLp gu (ENNReal.ofReal (6 : ℝ)) μ := by
    simpa using hgu6
  have hgu3 : MemLp gu (ENNReal.ofReal (3 : ℝ)) μ :=
    hgu6'.mono_exponent (by norm_num)
  simpa [gu, μ] using hgu3

private theorem lpNorm_eq_restrict_of_support_slice
    {g : Vec3 → ℝ} {B : Set Vec3}
    (_ : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hB : MeasurableSet B) (hzero : ∀ x ∉ B, g x = 0) :
    lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume =
      lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) := by
  have hind : B.indicator g =ᵐ[volume] g := by
    filter_upwards [] with x
    by_cases hx : x ∈ B
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hzero x hx]
  rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
  exact congrArg ENNReal.toReal (calc
    eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume =
        eLpNorm (B.indicator g) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      (eLpNorm_congr_ae hind.symm)
    _ = eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict B) := eLpNorm_indicator_eq_eLpNorm_restrict hB)

/-- For almost every time in a cylinder, the velocity has spatial `L³` norm on
the cylinder's ball. -/
theorem velocity_norm_memLp_three_ae_on_ball_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, s)))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hball : vec3Ball z.1 ρ ⊆ Ω' := by
    intro y hy
    have hz : (y, z.2) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨by linarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hcyl hz).1
  have htime : Ioc (z.2 - ρ ^ 2) z.2 ⊆ J := by
    intro s hs
    have hx : z.1 ∈ vec3Ball z.1 ρ := by
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (z.1, s) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs⟩
    exact (hcyl hz).2
  obtain ⟨_, _, _, _, _, _, _, _, hgrad⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hgradAll : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) := by
    filter_upwards [hgrad 0, hgrad 1, hgrad 2] with s h0 h1 h2
    intro i
    fin_cases i <;> assumption
  have hsliceJ := slice_memLp_ae_of_sws hsol hbox
  have hslice : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω') :=
    ae_restrict_of_ae_restrict_of_subset htime hsliceJ
  have hgradI := ae_restrict_of_ae_restrict_of_subset htime hgradAll
  filter_upwards [hslice, hgradI] with s hs hg
  exact velocity_norm_memLp_three_on_ball_of_slices hρ hball hs.1 hs.2 (hg ·)


/-- A spatial `L³` velocity slice gives global `L^{3/2}` and compact support
for each cut-off tensor entry.  The summed source norm is bounded by the tensor
energy with the dimension factor included. -/
theorem pressureUTensor_source_data_of_memLp_three
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {η : Vec3 → ℝ} {x₀ : Vec3} {ρ s : ℝ} (_ : 0 < ρ)
    (hηmeas : AEStronglyMeasurable η volume)
    (hηc : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ vec3Ball x₀ ρ)
    (hηbound : ∀ y, |η y| ≤ 1)
    (humeas : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hu : MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, s)))
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x₀ ρ))) :
    (∀ i j : Fin 3, MemLp
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) ∧
    (∀ i j : Fin 3, HasCompactSupport
      (fun y => η y * pressureUTensor u c (y, s) i j)) ∧
    (∑ i, ∑ j, lpNorm
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤
      (27 * (∫ y in vec3Ball x₀ ρ,
        pressureUTensorNorm u c s y ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  let μ : Measure Vec3 := volume.restrict B
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball x₀ ρ) < ∞)
  have : IsFiniteMeasure μ := ⟨hμtop⟩
  have hu' : MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, s)))
      (ENNReal.ofReal (3 : ℝ)) μ := by
    simpa [B, μ] using hu
  have humeas' : AEStronglyMeasurable (fun y : Vec3 => u (y, s)) μ := by
    simpa [B, μ] using humeas
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, s))
  have hc3 : MemLp (fun _ : Vec3 => vec3EuclideanNorm (c s))
      (ENNReal.ofReal (3 : ℝ)) μ := memLp_const _
  have hsum3 : MemLp (fun y => gu y + vec3EuclideanNorm (c s))
      (ENNReal.ofReal (3 : ℝ)) μ := by
    exact hu'.add hc3
  have : (ENNReal.ofReal (3 : ℝ)).HolderTriple
      (ENNReal.ofReal (3 : ℝ)) (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have hmajor : MemLp (fun y => gu y *
      (gu y + vec3EuclideanNorm (c s)))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := hu'.mul hsum3
  have humeasNorm : AEStronglyMeasurable gu μ := by
    exact (continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
      humeas'.aemeasurable).aestronglyMeasurable
  have hUmeas (i j : Fin 3) : AEStronglyMeasurable
      (fun y => pressureUTensor u c (y, s) i j) μ := by
    let F : Vec3 → ℝ := fun v => -v i * (v j - c s j)
    have hF : Continuous F := by
      dsimp [F]
      fun_prop
    exact (hF.measurable.comp_aemeasurable humeas'.aemeasurable).aestronglyMeasurable
  have hU32 (i j : Fin 3) : MemLp
      (fun y => pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
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
        rw [Real.norm_eq_abs]
        unfold pressureUTensor
        apply congrArg abs
        ring
      _ ≤ |u (y, s) i * u (y, s) j| + |c s j * u (y, s) i| := by
        simpa only [abs_neg] using
          (abs_add_le (-(u (y, s) i * u (y, s) j))
            (c s j * u (y, s) i))
      _ ≤ gu y * (gu y + vec3EuclideanNorm (c s)) := by
        rw [abs_mul, abs_mul]
        nlinarith only [hui, huj, hcj, abs_nonneg (u (y, s) i),
          abs_nonneg (u (y, s) j), abs_nonneg (c s j)]
      _ = ‖gu y * (gu y + vec3EuclideanNorm (c s))‖ := by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (vec3EuclideanNorm_nonneg _),
          abs_of_nonneg (add_nonneg (vec3EuclideanNorm_nonneg _)
            (vec3EuclideanNorm_nonneg _))]
  have hηmeas' : AEStronglyMeasurable η μ :=
    hηmeas.mono_measure Measure.restrict_le_self
  have hGμ (i j : Fin 3) : MemLp
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply (hU32 i j).of_le_mul (hηmeas'.mul (hUmeas i j))
    on_goal 1 => filter_upwards [] with y
    change |η y * pressureUTensor u c (y, s) i j| ≤
      1 * ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hηbound y) (abs_nonneg _)
  have hGc : ∀ i j : Fin 3, HasCompactSupport
      (fun y => η y * pressureUTensor u c (y, s) i j) := by
    intro i j
    exact hηc.mul_right
  have hG : ∀ i j : Fin 3, MemLp
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro i j
    apply CKN.memLp_three_halves_of_restrict_of_tsupport_subset (hGμ i j)
    exact (tsupport_mul_subset_left (f := η)
      (g := fun y => pressureUTensor u c (y, s) i j)).trans hηsupport
  have hpnormmeas : AEStronglyMeasurable
      (fun y => pressureUTensorNorm u c s y) μ := by
    let F : Vec3 → ℝ := fun v => Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      (-v i * (v j - c s j)) ^ (2 : ℕ))
    have hF : Continuous F := by
      dsimp [F]
      fun_prop
    exact (hF.measurable.comp_aemeasurable humeas'.aemeasurable).aestronglyMeasurable
  have hUnorm : MemLp (fun y => pressureUTensorNorm u c s y)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply hmajor.of_le hpnormmeas
    filter_upwards [] with y
    have hpnonn : 0 ≤ pressureUTensorNorm u c s y := by
      unfold pressureUTensorNorm
      positivity
    rw [Real.norm_of_nonneg hpnonn]
    rw [CKN.pressureUTensorNorm_eq_mul]
    have hdiff : vec3EuclideanNorm (u (y, s) - c s) ≤
        gu y + vec3EuclideanNorm (c s) := by
      simpa [gu, sub_eq_add_neg, vec3EuclideanNorm_eq_l2] using
        (vec3_norm_add_le_slice_velocity (u (y, s)) (-(c s)))
    change gu y * vec3EuclideanNorm (u (y, s) - c s) ≤
      ‖gu y * (gu y + vec3EuclideanNorm (c s))‖
    calc
      gu y * vec3EuclideanNorm (u (y, s) - c s) ≤
          gu y * (gu y + vec3EuclideanNorm (c s)) :=
        mul_le_mul_of_nonneg_left hdiff (vec3EuclideanNorm_nonneg _)
      _ = ‖gu y * (gu y + vec3EuclideanNorm (c s))‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (vec3EuclideanNorm_nonneg _) (add_nonneg
            (vec3EuclideanNorm_nonneg _) (vec3EuclideanNorm_nonneg _)))]
  have hpower : lpNorm (fun y => pressureUTensorNorm u c s y)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      (∫ y in B, pressureUTensorNorm u c s y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    have hEq : (∫ y in B, pressureUTensorNorm u c s y ^ (3 / 2 : ℝ)) =
        lpNorm (fun y => pressureUTensorNorm u c s y)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ ^ (3 / 2 : ℝ) := by
      have h := integral_rpow_norm_eq_lpNorm_rpow
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (μ := μ)
        (by norm_num) (by norm_num) hUnorm
      have hn : ∀ y, |pressureUTensorNorm u c s y| =
          pressureUTensorNorm u c s y :=
        fun y => abs_of_nonneg (Real.sqrt_nonneg _)
      simpa only [Real.norm_eq_abs, hn, ENNReal.toReal_ofReal (by norm_num :
        (0 : ℝ) ≤ 3 / 2)] using h
    have hfinal : lpNorm (fun y => pressureUTensorNorm u c s y)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ =
        (lpNorm (fun y => pressureUTensorNorm u c s y)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ ^ (3 / 2 : ℝ)) ^
            (2 / 3 : ℝ) := by
      rw [← Real.rpow_mul (lpNorm_nonneg) (3 / 2 : ℝ) (2 / 3 : ℝ),
        show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one]
    rw [hfinal, ← hEq]
  have hentry (i j : Fin 3) :
      lpNorm (fun y => η y * pressureUTensor u c (y, s) i j)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        (∫ y in B, pressureUTensorNorm u c s y ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) := by
    have hmono : lpNorm (fun y => η y * pressureUTensor u c (y, s) i j)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
        lpNorm (fun y => pressureUTensorNorm u c s y)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
      apply lpNorm_mono_real hUnorm
      intro y
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |η y| * |pressureUTensor u c (y, s) i j| ≤
            1 * |pressureUTensor u c (y, s) i j| :=
          mul_le_mul_of_nonneg_right (hηbound y) (abs_nonneg _)
        _ = |pressureUTensor u c (y, s) i j| := one_mul _
        _ ≤ pressureUTensorNorm u c s y := by
          exact pressure_component_abs_le_utensorNorm u c s y i j
    exact (lpNorm_eq_restrict_of_support_slice (hG i j)
      (vec3Ball_measurable x₀ ρ) (fun y hy => by
        have hηzero : η y = 0 := image_eq_zero_of_notMem_tsupport
          (fun hyt => hy (hηsupport hyt))
        simp [hηzero])).symm ▸ hmono.trans hpower
  have hA : 0 ≤ ∫ y in B, pressureUTensorNorm u c s y ^ (3 / 2 : ℝ) :=
    integral_nonneg (fun y => by
      unfold pressureUTensorNorm
      positivity)
  refine ⟨hG, hGc, ?_⟩
  calc
    (∑ i, ∑ j, lpNorm
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3,
          (∫ y in B, pressureUTensorNorm u c s y ^ (3 / 2 : ℝ)) ^
            (2 / 3 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = 9 * (∫ y in B, pressureUTensorNorm u c s y ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ]
      ring
    _ = (27 * (∫ y in B, pressureUTensorNorm u c s y ^ (3 / 2 : ℝ))) ^
          (2 / 3 : ℝ) := by
      have h27 : (27 : ℝ) ^ (2 / 3 : ℝ) = 9 := by
        have hbase : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
        rw [hbase, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      rw [Real.mul_rpow (by norm_num) hA, h27]

/-- The suitable-solution source package on almost every time slice of a
cylinder, in the component-sum form used by the unconditional endpoint. -/
theorem pressureUTensor_source_data_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i j : Fin 3, MemLp
        (fun x => mollifiedBallCutoff z.1 hρ x *
          pressureUTensor u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            (x, s) i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) ∧
      (∀ i j : Fin 3, HasCompactSupport
        (fun x => mollifiedBallCutoff z.1 hρ x *
          pressureUTensor u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            (x, s) i j)) ∧
      (∑ i, ∑ j, lpNorm
        (fun x => mollifiedBallCutoff z.1 hρ x *
          pressureUTensor u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            (x, s) i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤
        (27 * (∫ y in vec3Ball z.1 ρ,
          pressureUTensorNorm u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            s y ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j => MeasureTheory.average
    (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  have hηmeas : AEStronglyMeasurable η volume :=
    (mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable.aestronglyMeasurable
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ :=
    pressure_cutoff_support_subset_ball z.1 hρ
  have hηbound : ∀ y, |η y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ y)]
    exact mollifiedBallCutoff_le_one z.1 hρ y
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hu3 := velocity_norm_memLp_three_ae_on_ball_of_sws hsol hρ hsub
  have hslice := ae_restrict_of_ae_restrict_of_subset htime
    (slice_memLp_ae_of_sws hsol hbox)
  filter_upwards [hu3, hslice] with s hsU hsSlice
  have humeas := hsSlice.1.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono_set volume hball)
  obtain ⟨hG, hGc, hsource⟩ := pressureUTensor_source_data_of_memLp_three
    (u := u) (c := c) (η := η) (x₀ := z.1) (ρ := ρ) (s := s) hρ
    hηmeas hηc hηsupport hηbound humeas hsU
  exact ⟨by simpa [η, c] using hG, by simpa [η, c] using hGc,
    by simpa [η, c] using hsource⟩

end CKN
