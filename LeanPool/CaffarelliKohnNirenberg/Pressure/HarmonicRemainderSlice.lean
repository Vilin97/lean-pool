/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorDisplays
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34Solution

/-!
# Harmonic Remainder Slice

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private lemma euclideanBall_eq_vec3Ball_harmonic {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

private lemma euclideanBall_measurable_harmonic (x₀ : Vec3) (r : ℝ) :
    MeasurableSet (euclideanBall x₀ r) := by
  change MeasurableSet {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
  exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
    continuous_const).measurableSet

private lemma harmonic_vecEuclideanNorm_eq_l2 (a : Vec3) :
    vecEuclideanNorm a = ‖WithLp.toLp 2 a‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private lemma harmonic_vecNorm_add_le (a b : Vec3) :
    vecEuclideanNorm (a + b) ≤ vecEuclideanNorm a + vecEuclideanNorm b := by
  rw [harmonic_vecEuclideanNorm_eq_l2, harmonic_vecEuclideanNorm_eq_l2,
    harmonic_vecEuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private lemma harmonic_inner_subset_outer {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) :
    euclideanBall x₀ (13 * ρ / 20) ⊆ euclideanBall x₀ ρ := by
  intro x hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
  exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx).trans_le
    (by linarith only [hρ])

private lemma harmonic_local_ball_subset_inner {x₀ x : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (ρ / 2)) :
    euclideanBall x (ρ / 10) ⊆ euclideanBall x₀ (13 * ρ / 20) := by
  intro y hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have htri : vecEuclideanNorm (y - x₀) ≤
      vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) := by
    rw [show y - x₀ = (y - x) + (x - x₀) by abel]
    exact harmonic_vecNorm_add_le _ _
  calc
    vecEuclideanNorm (y - x₀) ≤
        vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) := htri
    _ < ρ / 10 + ρ / 2 := by linarith only [hy', hx']
    _ ≤ 13 * ρ / 20 := by linarith only [hρ]

private lemma harmonic_inner_local_open (x : Vec3) (ρ : ℝ) :
    IsOpen (euclideanBall x (ρ / 20)) := by
  exact (isOpen_lt (contDiff_euclideanSqDist_left x).continuous
    continuous_const)

private lemma harmonic_lpNorm_inner_le_global
    {f : Vec3 → ℝ} {x₀ : Vec3} {r : ℝ} {p : ENNReal}
    (hf : MemLp f p volume) :
    lpNorm f p (volume.restrict (euclideanBall x₀ r)) ≤ lpNorm f p volume := by
  rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
  exact ENNReal.toReal_mono hf.eLpNorm_lt_top.ne
    (eLpNorm_mono_measure f Measure.restrict_le_self)

/-- The local-ball form of the harmonic gradient display.  It is the form used
by the slice estimate when harmonicity is known on the smaller inner ball. -/
theorem harmonic_remainder_local_gradient_display
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))))
    (hweak : WeaklyHarmonicOn
      (euclideanBall x₀ (13 * ρ / 20)) h)
    (hsmooth : ContDiffOn ℝ (1 : ℕ∞) h
      (euclideanBall x₀ (ρ / 2))) :
    ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm (classicalGradient h x) ≤
        (1000 * harmonicInteriorDisplayConstant) * (ρ ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
  intro x hx
  let B : Set Vec3 := euclideanBall x (ρ / 10)
  let Bhalf : Set Vec3 := euclideanBall x (ρ / 20)
  have hBsub : B ⊆ euclideanBall x₀ (13 * ρ / 20) := by
    exact harmonic_local_ball_subset_inner hρ hx
  have hmemB := hmem.mono_measure
    (Measure.restrict_mono_set volume hBsub)
  have hweakB : WeaklyHarmonicOn B h := by
    exact local_weak_harmonic hBsub hweak
  obtain ⟨H, hHsmooth, hHae, _hHvalue, hHgrad, _hHplain, _hHsharp⟩ :=
    weak_harmonic_interior_displays (x₀ := x) (ρ := ρ / 10)
      (by positivity) hmemB hweakB
  have hBhalfopen : IsOpen Bhalf := by
    dsimp [Bhalf]
    exact harmonic_inner_local_open x ρ
  have hBhalf_eq : Bhalf = euclideanBall x (ρ / 10 / 2) := by
    dsimp [Bhalf]
    congr 1
    ring
  let V : Set Vec3 := Bhalf ∩ euclideanBall x₀ (ρ / 2)
  have hVopen : IsOpen V := hBhalfopen.inter (by
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
      continuous_const))
  have hxV : x ∈ V := by
    refine ⟨?_, hx⟩
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    rw [sub_self]
    simpa [vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (div_pos hρ (by norm_num : (0 : ℝ) < 20))
  have hHaeBhalf : h =ᵐ[volume.restrict Bhalf] H := by
    rw [hBhalf_eq]
    exact hHae
  have hHaeV : h =ᵐ[volume.restrict V] H :=
    ae_mono (Measure.restrict_mono_set volume inter_subset_left) hHaeBhalf
  have hHcont : ContinuousOn H Bhalf := by
    rw [hBhalf_eq]
    exact hHsmooth.continuousOn
  have hxeq : EqOn h H V :=
    Measure.eqOn_open_of_ae_eq hHaeV hVopen
      (hsmooth.mono inter_subset_right |>.continuousOn)
      (hHcont.mono inter_subset_left)
  have hxeq' : h =ᶠ[𝓝 x] H := by
    filter_upwards [hVopen.mem_nhds hxV] with y hy
    exact hxeq hy
  have hfd := hxeq'.fderiv_eq (𝕜 := ℝ)
  have hgrad_eq : classicalGradient h x = classicalGradient H x := by
    funext i
    simp only [classicalGradient_apply]
    rw [hfd]
  rw [hgrad_eq]
  have hlocal : lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict B) ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) :=
    lpNorm_restrict_mono hBsub hmem
  have hdisp := hHgrad x (by
    rw [← hBhalf_eq]
    exact hxV.1)
  calc
    vec3EuclideanNorm (classicalGradient H x) ≤
        harmonicInteriorDisplayConstant * ((ρ / 10) ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) := hdisp
    _ ≤ harmonicInteriorDisplayConstant * ((ρ / 10) ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
      have hcoef : 0 ≤ harmonicInteriorDisplayConstant * ((ρ / 10) ^ 3)⁻¹ := by
        exact mul_nonneg harmonicInteriorDisplayConstant_nonneg (by positivity)
      exact mul_le_mul_of_nonneg_left hlocal hcoef
    _ = (1000 * harmonicInteriorDisplayConstant) * (ρ ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
      field_simp [ne_of_gt hρ]
      ring

/-- The same display with the numerical constant exposed before the data. -/
theorem harmonic_remainder_gradient_display
    (C₁₇ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))))
    (hweak : WeaklyHarmonicOn
      (euclideanBall x₀ (13 * ρ / 20)) h)
    (hsmooth : ContDiffOn ℝ (1 : ℕ∞) h
      (euclideanBall x₀ (ρ / 2))) :
    ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm (classicalGradient h x) ≤
        C₁₇ * (ρ ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
  have hbase := harmonic_remainder_local_gradient_display hρ hmem hweak hsmooth
  intro x hx
  calc
    vec3EuclideanNorm (classicalGradient h x) ≤
        (1000 * harmonicInteriorDisplayConstant) * (ρ ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := hbase x hx
    _ ≤ C₁₇ * (ρ ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
      have hscaled := mul_le_mul_of_nonneg_right hC₁₇
        (inv_nonneg.mpr (by positivity : 0 ≤ ρ ^ 3))
      calc
        (1000 * harmonicInteriorDisplayConstant) * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) =
            ((1000 * harmonicInteriorDisplayConstant) * (ρ ^ 3)⁻¹) *
              lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by ring
        _ ≤ (C₁₇ * (ρ ^ 3)⁻¹) *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) :=
          mul_le_mul_of_nonneg_right hscaled lpNorm_nonneg
        _ = C₁₇ * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by ring


/-- The harmonic remainder is the difference of the pressure, the first
pressure part, and the two force parts on the inner ball. -/
theorem harmonic_remainder_memLp_of_inner_decomposition
    {h p p₁ p₇₈ : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hp₇₈ : MemLp p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))))
    (hdecomp : h =ᵐ[volume.restrict (euclideanBall x₀ (13 * ρ / 20))]
      ((fun x => p x) - p₁ - p₇₈)) :
    MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
  have hpinner := hp.mono_measure (Measure.restrict_mono_set volume
    (harmonic_inner_subset_outer hρ))
  have hp₁inner := hp₁.mono_measure
    (μ := volume) (ν := volume.restrict (euclideanBall x₀ (13 * ρ / 20)))
    Measure.restrict_le_self
  have hsub : MemLp ((fun x => p x) - p₁ - p₇₈)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
    exact (hpinner.sub hp₁inner).sub hp₇₈
  exact hsub.ae_eq hdecomp.symm

/-- The (L^{3/2}) triangle estimate for the harmonic remainder. -/
theorem harmonic_remainder_inner_lpNorm_le
    {h p p₁ p₇₈ : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hp₇₈ : MemLp p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))))
    (hdecomp : h =ᵐ[volume.restrict (euclideanBall x₀ (13 * ρ / 20))]
      ((fun x => p x) - p₁ - p₇₈)) :
    lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) ≤
      lpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) +
      lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume +
      lpNorm p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
  have hmem := harmonic_remainder_memLp_of_inner_decomposition hρ hp hp₁ hp₇₈ hdecomp
  have hpinner := hp.mono_measure (Measure.restrict_mono_set volume
    (harmonic_inner_subset_outer hρ))
  have hp₁inner := hp₁.mono_measure
    (μ := volume) (ν := volume.restrict (euclideanBall x₀ (13 * ρ / 20)))
    Measure.restrict_le_self
  have hfirst := lpNorm_sub_le (f := p) (g := p₁) hpinner (by norm_num)
  have hsecond := lpNorm_sub_le (f := (fun x => p x) - p₁) (g := p₇₈)
    (hpinner.sub hp₁inner) (by norm_num)
  have hnorm : lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) =
    lpNorm ((fun x => p x) - p₁ - p₇₈)
      (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
    rw [lpNorm, lpNorm, eLpNorm_congr_ae hdecomp]
  calc
    _ = lpNorm ((fun x => p x) - p₁ - p₇₈)
        (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := hnorm
    _ ≤ lpNorm ((fun x => p x) - p₁)
        (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) +
        lpNorm p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := hsecond
    _ ≤ (lpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) +
        lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume) +
        lpNorm p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ (13 * ρ / 20))) := by
      gcongr
      · exact hfirst.trans (add_le_add
          (lpNorm_restrict_mono (harmonic_inner_subset_outer hρ) hp)
          (harmonic_lpNorm_inner_le_global hp₁))

/-- The a.e.-time harmonicity and inner-ball integrability package for a
suitable weak solution.  The p₁ certificate and the p₇+p₈ certificate are
deliberately supplied by their respective pressure estimates. -/
theorem harmonic_remainder_slice_data_ae_of_sws
    {C₁₁ : ℝ} {E F : ℝ → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * (E s) ^ (2 / 3 : ℝ))
    (hP78 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤ F s) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
          (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p s) ∧
      MemLp (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
        lpNorm (fun x : Vec3 => p (x, s))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 ρ)) + C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s := by
  have hp := sws_pressure_memLp_slice_ae hsol hρ hsub
  rw [← euclideanBall_eq_vec3Ball_harmonic
    (x₀ := z.1) (r := ρ) hρ] at hp
  have hdata := pressure_harmonic_potential_data_ae_of_sws_inner hsol hρ hsub
  filter_upwards [hp, hdata, hCZ_p1, hP78] with s hs hpdata hsCZ hsP78
  have hweak := harmonicPressurePart_weaklyHarmonicOn_of_data hpdata
  have hdecomp := pressure_remainder_eq_on_inner
    (u := u)
    (c := fun t j => average (volume.restrict (vec3Ball z.1 ρ))
      (fun y : Vec3 => u (y, t) j))
    (p := p) (f := f) (x₀ := z.1) (ρ := ρ) (s := s) hρ
  have hmem := harmonic_remainder_memLp_of_inner_decomposition hρ hs
    hsCZ.1 hsP78.1 hdecomp
  have htri := harmonic_remainder_inner_lpNorm_le hρ hs hsCZ.1 hsP78.1 hdecomp
  refine ⟨hweak, hmem, ?_⟩
  calc
    lpNorm (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
      lpNorm (fun x : Vec3 => p (x, s))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 ρ)) +
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume +
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) := htri
    _ ≤ lpNorm (fun x : Vec3 => p (x, s))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 ρ)) + C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s := by
      gcongr
      · exact hsCZ.2
      · exact hsP78.2

private theorem harmonic_remainder_gradient_eLpNorm_le_of_sup_aux
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ C L : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hmem : MemLp (fun x => classicalGradient h x)
      (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (euclideanBall x₀ (ρ / 2))))
    (hsup : ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm (classicalGradient h x) ≤ C * L) :
    eLpNorm (fun x => classicalGradient h x)
        (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
      ENNReal.ofReal (C * L) *
        (volume (euclideanBall x₀ (ρ / 2))) ^ (5 / 6 : ℝ) := by
  let B : Set Vec3 := euclideanBall x₀ (ρ / 2)
  let μ : Measure Vec3 := volume.restrict B
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    exact euclideanBall_measurable_harmonic x₀ (ρ / 2)
  let _ : IsFiniteMeasure μ := by
    refine isFiniteMeasure_restrict.mpr ?_
    rw [show B = vec3Ball x₀ (ρ / 2) by
      dsimp [B]
      exact euclideanBall_eq_vec3Ball_harmonic (by positivity)]
    rw [volume_vec3Ball_eq]
    finiteness
  have hbound : ∀ᵐ x ∂μ,
      ‖classicalGradient h x‖ ≤ C * L := by
    filter_upwards [ae_restrict_mem hBmeas] with x hx
    have hspace : ‖classicalGradient h x‖ ≤
        vec3EuclideanNorm (classicalGradient h x) := by
      simpa only [spaceEuclideanNorm, vec3EuclideanNorm] using
        space_norm_le_euclideanNorm (classicalGradient h x)
    exact hspace.trans (hsup x hx)
  have hconst : eLpNorm (fun _ : Vec3 => (C * L : ℝ))
      (ENNReal.ofReal (6 / 5 : ℝ)) μ =
      ENNReal.ofReal (C * L) * (volume B) ^ (5 / 6 : ℝ) := by
    rw [eLpNorm_const (C * L) (by norm_num)]
    · rw [Measure.restrict_apply_univ]
      simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)]
      congr 1
      · calc
          ‖C * L‖ₑ = ENNReal.ofReal ‖C * L‖ := (ofReal_norm _).symm
          _ = ENNReal.ofReal (C * L) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hL)]
      · norm_num
    · intro hzero
      have hzero' : volume B = 0 := by
        simpa [μ, Measure.restrict_apply_univ] using hzero
      rw [show B = vec3Ball x₀ (ρ / 2) by
        dsimp [B]
        exact euclideanBall_eq_vec3Ball_harmonic (by positivity)] at hzero'
      rw [volume_vec3Ball_eq] at hzero'
      have hpos : 0 < ENNReal.ofReal (ρ / 2) ^ 3 *
          ENNReal.ofReal (Real.pi * 4 / 3) := by positivity
      exact hpos.ne' hzero'
  have hmem' : MemLp (fun x => classicalGradient h x)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ := by simpa [μ, B] using hmem
  have hbound' : ∀ᵐ x ∂μ,
      ‖classicalGradient h x‖ ≤ ‖(fun _ : Vec3 => (C * L : ℝ)) x‖ := by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hL)] using hx
  have hmono : eLpNorm (fun x => classicalGradient h x)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm (fun _ : Vec3 => (C * L : ℝ))
        (ENNReal.ofReal (6 / 5 : ℝ)) μ :=
    eLpNorm_mono_ae (p := ENNReal.ofReal (6 / 5 : ℝ))
      (g := fun _ : Vec3 => (C * L : ℝ)) hmem'.aestronglyMeasurable hbound'
  rw [hconst] at hmono
  simpa [μ, B] using hmono

/-- The slice gradient estimate and its (L^{6/5}) consequence.  The two
regularity hypotheses are the representative and slice-membership interfaces;
the force estimate itself remains an explicit p₇+p₈ input. -/
theorem harmonic_remainder_gradient_eLpNorm_ae_of_sws
    (C₁₇ C₁₁ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    {E F : ℝ → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hC₁₁ : 0 ≤ C₁₁) (hE : ∀ s, 0 ≤ E s) (hF : ∀ s, 0 ≤ F s)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * (E s) ^ (2 / 3 : ℝ))
    (hP78 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤ F s)
    (hregular : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ContDiffOn ℝ (1 : ℕ∞)
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)
        (euclideanBall z.1 (ρ / 2)))
    :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ x ∈ euclideanBall z.1 (ρ / 2),
        vec3EuclideanNorm (classicalGradient
            (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) p s) x) ≤
          C₁₇ * (ρ ^ 3)⁻¹ *
            (lpNorm (fun x : Vec3 => p (x, s))
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall z.1 ρ)) +
              C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s)) ∧
      eLpNorm (fun x => classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p s) x)
        (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
        ENNReal.ofReal ((C₁₇ * (ρ ^ 3)⁻¹) *
          (lpNorm (fun x : Vec3 => p (x, s))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall z.1 ρ)) +
            C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s)) *
          (volume (euclideanBall z.1 (ρ / 2))) ^ (5 / 6 : ℝ) := by
  have hdata := harmonic_remainder_slice_data_ae_of_sws
    (C₁₁ := C₁₁) (E := E) (F := F) hsol hρ hsub hCZ_p1 hP78
  filter_upwards [hdata, hregular] with s hs hsreg
  rcases hs with ⟨hweak, hmem, hbound⟩
  have hC₁₇nonneg : 0 ≤ C₁₇ := by
    have hbase : 0 ≤ 1000 * harmonicInteriorDisplayConstant :=
      mul_nonneg (by norm_num) harmonicInteriorDisplayConstant_nonneg
    exact hbase.trans hC₁₇
  let L : ℝ := lpNorm (fun x : Vec3 => p (x, s))
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall z.1 ρ)) +
      C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg
      (add_nonneg lpNorm_nonneg
        (mul_nonneg hC₁₁ (Real.rpow_nonneg (hE s) _))) (hF s)
  have hpoint : ∀ x ∈ euclideanBall z.1 (ρ / 2),
      vec3EuclideanNorm (classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p s) x) ≤
        C₁₇ * (ρ ^ 3)⁻¹ * L := by
    intro x hx
    have hdisplay := harmonic_remainder_gradient_display C₁₇ hC₁₇ hρ
      hmem hweak hsreg
    calc
      _ ≤ C₁₇ * (ρ ^ 3)⁻¹ *
          lpNorm (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p s)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) :=
        hdisplay x hx
      _ ≤ C₁₇ * (ρ ^ 3)⁻¹ * L := by
        exact mul_le_mul_of_nonneg_left hbound
          (mul_nonneg hC₁₇nonneg (inv_nonneg.mpr (by positivity)))
  let B : Set Vec3 := euclideanBall z.1 (ρ / 2)
  have hBopen : IsOpen B := by
    dsimp [B]
    exact isOpen_lt (contDiff_euclideanSqDist_left z.1).continuous continuous_const
  have hgradcont : ContinuousOn (classicalGradient
      (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p s)) B := by
    intro x hx
    have hfderiv := hsreg.continuousOn_fderiv_of_isOpen hBopen
      (by norm_num : (1 : WithTop ℕ∞) ≤ (1 : ℕ∞))
    have hcont : ContinuousWithinAt
        (fderiv ℝ (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)) B x := hfderiv x hx
    have heval : Continuous
        (fun A : (Vec3 →L[ℝ] ℝ) => fun i : Fin 3 => A (basisVec i)) := by
      fun_prop
    change ContinuousWithinAt
      ((fun A : (Vec3 →L[ℝ] ℝ) => fun i : Fin 3 => A (basisVec i)) ∘
        fderiv ℝ (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)) B x
    exact heval.continuousAt.continuousWithinAt.comp hcont
      (fun _ _ => Set.mem_univ _)
  have hgradmeas : AEStronglyMeasurable (classicalGradient
      (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p s))
      (volume.restrict B) := hgradcont.aestronglyMeasurable hBopen.measurableSet
  let _ : IsFiniteMeasure (volume.restrict B) := by
    refine isFiniteMeasure_restrict.mpr ?_
    rw [show B = vec3Ball z.1 (ρ / 2) by
      dsimp [B]
      exact euclideanBall_eq_vec3Ball_harmonic (by positivity)]
    rw [volume_vec3Ball_eq]
    finiteness
  have hgradmem : MemLp (fun x => classicalGradient
      (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p s) x)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) := by
    apply MemLp.of_bound hgradmeas (C₁₇ * (ρ ^ 3)⁻¹ * L)
    filter_upwards [ae_restrict_mem hBopen.measurableSet] with x hx
    exact (space_norm_le_euclideanNorm _).trans (hpoint x hx)
  have hnorm := harmonic_remainder_gradient_eLpNorm_le_of_sup_aux
    (x₀ := z.1) (ρ := ρ) (C := C₁₇ * (ρ ^ 3)⁻¹) (L := L)
    hρ (mul_nonneg hC₁₇nonneg (inv_nonneg.mpr (by positivity))) hL
      (by simpa [B] using hgradmem) hpoint
  refine ⟨?_, ?_⟩
  · simpa [L] using hpoint
  · simpa [L, mul_assoc] using hnorm

end CKN
