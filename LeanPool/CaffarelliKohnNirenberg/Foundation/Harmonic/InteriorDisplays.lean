/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorDisplayBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Mean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence

/-!
# Interior Displays

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

/-! The source-level representative has the larger value display and the
gradient display on the concentric half-ball.  Its values in the outer part
are chosen from the local weak representatives used in the proof. -/
private lemma weak_harmonic_interior_rep
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ H : Vec3 → ℝ,
      ContDiffOn ℝ (1 : ℕ∞) H (euclideanBall x₀ (ρ / 2)) ∧
      h =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 2))] H ∧
      (∀ x ∈ euclideanBall x₀ (3 * ρ / 4),
        |H x| ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        |H x| ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        vec3EuclideanNorm (classicalGradient H x) ≤
          harmonicInteriorDisplayConstant * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        vec3EuclideanNorm (classicalGradient H x) ≤
          1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) := by
  classical
  obtain ⟨H₀, hH₀diff, hH₀ae, hH₀bound, hH₀grad⟩ :=
    weakly_harmonic_interior_smooth hρ hmem hweak
  let I : Set Vec3 := euclideanBall x₀ (ρ / 2)
  let O : Set Vec3 := euclideanBall x₀ (3 * ρ / 4)
  have hIopen : IsOpen I := by
    dsimp [I]
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  let v : ∀ x : Vec3, x ∈ O → ℝ := fun x hx =>
    Classical.choose (local_value_bound hρ hx hmem hweak)
  have hv : ∀ x (hx : x ∈ O), |v x hx| ≤
      576 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    intro x hx
    exact Classical.choose_spec (local_value_bound hρ hx hmem hweak)
  let H : Vec3 → ℝ := fun x =>
    if hx : x ∈ I then H₀ x else
      if hxO : x ∈ O then v x hxO else 0
  have hHdiff : ContDiffOn ℝ (1 : ℕ∞) H I := by
    apply hH₀diff.congr
    intro x hx
    have hxI : x ∈ I := by simpa only [I] using hx
    simp [H, hxI]
  have hHae : h =ᵐ[volume.restrict I] H := by
    filter_upwards [hH₀ae, ae_restrict_mem hIopen.measurableSet] with x hx hxI
    rw [show H x = H₀ x by simp [H, hxI], hx]
  have hK : 0 ≤ weakHarmonicInteriorSupConstant :=
    weakHarmonicInteriorSupConstant_nonneg
  have hL : 0 ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)) := lpNorm_nonneg
  have hvalue : ∀ x ∈ O, |H x| ≤ harmonicInteriorDisplayConstant *
      (ρ ^ 2)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) := by
    intro x hx
    by_cases hxI : x ∈ I
    · have hb := hH₀bound x hxI
      calc
        |H x| = |H₀ x| := by simp [H, hxI]
        _ ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) := hb
        _ ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) := by
          have hCK : weakHarmonicInteriorSupConstant ≤
              harmonicInteriorDisplayConstant := by
            exact le_trans (le_max_left _ _) (le_max_left _ _)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCK (by positivity)) hL
    · have hb := hv x hx
      calc
        |H x| = |v x hx| := by simp [H, hxI, hx]
        _ ≤ 576 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) := hb
        _ ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) := by
          have hCK : 576 * weakHarmonicInteriorSupConstant ≤
              harmonicInteriorDisplayConstant := by
            exact le_trans (le_max_right _ _) (le_max_left _ _)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCK (by positivity)) hL
  have hvalueSharp : ∀ x ∈ I, |H x| ≤
      weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    intro x hx
    have hxI : x ∈ I := hx
    have hb := hH₀bound x hxI
    calc
      |H x| = |H₀ x| := by simp [H, hxI]
      _ ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) := hb
  have hgrad : ∀ x ∈ I, vec3EuclideanNorm (classicalGradient H x) ≤
      harmonicInteriorDisplayConstant * (ρ ^ 3)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    intro x hx
    have hxnhds : I ∈ 𝓝 x := hIopen.mem_nhds hx
    have heq : H =ᶠ[𝓝 x] H₀ := by
      filter_upwards [hxnhds] with y hy
      simp [H, hy]
    have hH₀at : ContDiffAt ℝ (1 : ℕ∞) H₀ x := hH₀diff.contDiffAt hxnhds
    have hderiv := (hH₀at.differentiableAt (by norm_num)).hasFDerivAt
    have hderivH := hderiv.congr_of_eventuallyEq heq
    have hfd : fderiv ℝ H x = fderiv ℝ H₀ x := by
      rw [hderivH.fderiv, hderiv.fderiv]
    have hgrad_eq : classicalGradient H x = classicalGradient H₀ x := by
      funext i
      simp only [classicalGradient_apply, hfd]
    rw [hgrad_eq]
    have hb := hH₀grad x hx
    have hCK : 1728 * harmonicInteriorGradientSupConstant ≤
        harmonicInteriorDisplayConstant := by
      exact le_trans (le_max_left _ _)
        (le_max_right (max weakHarmonicInteriorSupConstant
          (576 * weakHarmonicInteriorSupConstant)) _)
    calc
      vec3EuclideanNorm (classicalGradient H₀ x) ≤
          1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) := hb
      _ ≤ harmonicInteriorDisplayConstant * (ρ ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCK (by positivity)) hL
  have hgradSharp : ∀ x ∈ I, vec3EuclideanNorm (classicalGradient H x) ≤
      1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    intro x hx
    have hxnhds : I ∈ 𝓝 x := hIopen.mem_nhds hx
    have heq : H =ᶠ[𝓝 x] H₀ := by
      filter_upwards [hxnhds] with y hy
      simp [H, hy]
    have hH₀at : ContDiffAt ℝ (1 : ℕ∞) H₀ x := hH₀diff.contDiffAt hxnhds
    have hderiv := (hH₀at.differentiableAt (by norm_num)).hasFDerivAt
    have hderivH := hderiv.congr_of_eventuallyEq heq
    have hfd : fderiv ℝ H x = fderiv ℝ H₀ x := by
      rw [hderivH.fderiv, hderiv.fderiv]
    have hgrad_eq : classicalGradient H x = classicalGradient H₀ x := by
      funext i
      simp only [classicalGradient_apply, hfd]
    rw [hgrad_eq]
    exact hH₀grad x hx
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [I] using hHdiff
  · simpa only [I] using hHae
  · intro x hx
    exact hvalue x (by simpa only [O] using hx)
  · intro x hx
    exact hvalueSharp x (by simpa only [I] using hx)
  · intro x hx
    exact hgrad x (by simpa only [I] using hx)
  · intro x hx
    exact hgradSharp x (by simpa only [I] using hx)

/-! The four source displays, with one constant and no global smoothness
assumption on the weakly harmonic datum. -/
theorem weak_harmonic_interior_displays
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ H : Vec3 → ℝ,
      ContDiffOn ℝ (1 : ℕ∞) H (euclideanBall x₀ (ρ / 2)) ∧
      h =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 2))] H ∧
      (∀ x ∈ euclideanBall x₀ (3 * ρ / 4),
        |H x| ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        vec3EuclideanNorm (classicalGradient H x) ≤
          harmonicInteriorDisplayConstant * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ r : ℝ, 0 < r → r ≤ ρ / 2 →
        (r ^ 2)⁻¹ *
            ∫ y in euclideanBall x₀ r, |h y| ^ (3 / 2 : ℝ) ≤
          harmonicInteriorDisplayConstant * (r / ρ) * (ρ ^ 2)⁻¹ *
            ∫ y in euclideanBall x₀ ρ, |h y| ^ (3 / 2 : ℝ)) ∧
      (∀ r : ℝ, 0 < r → r ≤ ρ / 2 →
        (r ^ 2)⁻¹ *
            ∫ y in euclideanBall x₀ r,
              |h y - ⨍ z in euclideanBall x₀ r, h z ∂volume| ^
                (3 / 2 : ℝ) ≤
          harmonicInteriorDisplayConstant * (r / ρ) ^ (5 / 2 : ℝ) *
            (ρ ^ 2)⁻¹ *
              ∫ y in euclideanBall x₀ ρ, |h y| ^ (3 / 2 : ℝ)) := by
  classical
  obtain ⟨H, hHdiff, hHae, hHvalue, hHvalueSharp, hHgrad, hHgradSharp⟩ :=
    weak_harmonic_interior_rep hρ hmem hweak
  have hK : 0 ≤ weakHarmonicInteriorSupConstant :=
    weakHarmonicInteriorSupConstant_nonneg
  have hG : 0 ≤ harmonicInteriorGradientSupConstant :=
    harmonicInteriorGradientSupConstant_nonneg
  have hL : 0 ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)) := lpNorm_nonneg
  have hC : 0 ≤ harmonicInteriorDisplayConstant :=
    harmonicInteriorDisplayConstant_nonneg
  have henergy :
      (∫ y in euclideanBall x₀ ρ, |h y| ^ (3 / 2 : ℝ)) =
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) ^ (3 / 2 : ℝ) := by
    have hp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
      norm_num
    simpa only [Real.norm_eq_abs, hp] using
      (CKN.integral_rpow_norm_eq_lpNorm_rpow
        (by norm_num) (by norm_num) hmem)
  have hplain : ∀ r : ℝ, 0 < r → r ≤ ρ / 2 →
      (r ^ 2)⁻¹ *
          ∫ y in euclideanBall x₀ r, |h y| ^ (3 / 2 : ℝ) ≤
        harmonicInteriorDisplayConstant * (r / ρ) * (ρ ^ 2)⁻¹ *
          ∫ y in euclideanBall x₀ ρ, |h y| ^ (3 / 2 : ℝ) := by
    intro r hr hrr
    let Br : Set Vec3 := euclideanBall x₀ r
    have hBrmeas : MeasurableSet Br := by
      dsimp [Br]
      exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
        continuous_const).measurableSet
    have hBrI : Br ⊆ euclideanBall x₀ (ρ / 2) := by
      intro y hy
      change y ∈ euclideanBall x₀ r at hy
      have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      nlinarith only [hy', hrr]
    have hBrO : Br ⊆ euclideanBall x₀ (3 * ρ / 4) := by
      intro y hy
      change y ∈ euclideanBall x₀ r at hy
      have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      nlinarith only [hy', hrr, hρ]
    have hvol : volume Br ≠ ∞ := by
      dsimp [Br]
      rw [euclideanBall_eq_vec3Ball_display hr, volume_vec3Ball_eq]
      finiteness
    have hvolreal : (volume Br).toReal = (Real.pi * 4 / 3) * r ^ 3 := by
      dsimp [Br]
      rw [euclideanBall_eq_vec3Ball_display hr, volume_vec3Ball_eq]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ r),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
      ring
    let _ : IsFiniteMeasure (volume.restrict Br) :=
      isFiniteMeasure_restrict.mpr hvol
    have hmemBr := hmem.mono_measure
      (Measure.restrict_mono_set volume (by
        intro y hy
        change y ∈ euclideanBall x₀ r at hy
        have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
        nlinarith only [hy', hrr, hρ]))
    have hEqBr : h =ᵐ[volume.restrict Br] H :=
      ae_mono (Measure.restrict_mono_set volume hBrI) hHae
    have hpoint : ∀ᵐ y ∂volume.restrict Br,
        |h y| ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) := by
      filter_upwards [hEqBr, ae_restrict_mem hBrmeas] with y hyEq hy
      rw [hyEq]
      exact hHvalueSharp y (hBrI hy)
    have hint := set_integral_rpow_bound hmemBr hvol hpoint
    have hbound := mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ (r ^ 2)⁻¹)
    have hplainC : (Real.pi * 4 / 3) *
        weakHarmonicInteriorSupConstant ^ (3 / 2 : ℝ) ≤
        harmonicInteriorDisplayConstant := by
      dsimp [harmonicInteriorDisplayConstant]
      exact (le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    calc
      (r ^ 2)⁻¹ * ∫ y in Br, |h y| ^ (3 / 2 : ℝ) ≤
          (r ^ 2)⁻¹ * ((volume Br).toReal *
            (weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
              lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ ρ))) ^ (3 / 2 : ℝ)) := hbound
      _ = ((Real.pi * 4 / 3) *
          weakHarmonicInteriorSupConstant ^ (3 / 2 : ℝ)) * (r / ρ) *
            (ρ ^ 2)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) ^ (3 / 2 : ℝ) := by
        rw [hvolreal]
        exact plain_display_scaling hr hρ hK hL
      _ ≤ harmonicInteriorDisplayConstant * (r / ρ) * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) ^ (3 / 2 : ℝ) := by
        gcongr
      _ = harmonicInteriorDisplayConstant * (r / ρ) * (ρ ^ 2)⁻¹ *
          ∫ y in euclideanBall x₀ ρ, |h y| ^ (3 / 2 : ℝ) := by
        rw [henergy]

  have hosc : ∀ r : ℝ, 0 < r → r ≤ ρ / 2 →
      (r ^ 2)⁻¹ *
          ∫ y in euclideanBall x₀ r,
            |h y - ⨍ z in euclideanBall x₀ r, h z ∂volume| ^
              (3 / 2 : ℝ) ≤
        harmonicInteriorDisplayConstant * (r / ρ) ^ (5 / 2 : ℝ) *
          (ρ ^ 2)⁻¹ * ∫ y in euclideanBall x₀ ρ, |h y| ^ (3 / 2 : ℝ) := by
    intro r hr hrr
    let Br : Set Vec3 := euclideanBall x₀ r
    have hBrmeas : MeasurableSet Br := by
      dsimp [Br]
      exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
        continuous_const).measurableSet
    have hBrI : Br ⊆ euclideanBall x₀ (ρ / 2) := by
      intro y hy
      change y ∈ euclideanBall x₀ r at hy
      have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      nlinarith only [hy', hrr]
    have hvol : volume Br ≠ ∞ := by
      dsimp [Br]
      rw [euclideanBall_eq_vec3Ball_display hr, volume_vec3Ball_eq]
      finiteness
    have hvolpos : 0 < (volume Br).toReal := by
      dsimp [Br]
      rw [euclideanBall_eq_vec3Ball_display hr, volume_vec3Ball_eq]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ r),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
      positivity
    have hvolreal : (volume Br).toReal = (Real.pi * 4 / 3) * r ^ 3 := by
      dsimp [Br]
      rw [euclideanBall_eq_vec3Ball_display hr, volume_vec3Ball_eq]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ r),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
      ring
    let _ : IsFiniteMeasure (volume.restrict Br) :=
      isFiniteMeasure_restrict.mpr hvol
    have hmemBr := hmem.mono_measure
      (Measure.restrict_mono_set volume (by
        intro y hy
        change y ∈ euclideanBall x₀ r at hy
        have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
        nlinarith only [hy', hrr, hρ]))
    have hEqBr : h =ᵐ[volume.restrict Br] H :=
      ae_mono (Measure.restrict_mono_set volume hBrI) hHae
    have hHint : Integrable H (volume.restrict Br) :=
      (hmemBr.integrable (by norm_num)).congr hEqBr
    have hmean : ∀ x ∈ Br,
        |H x - ⨍ y in Br, H y ∂volume| ≤
          6 * (1728 * harmonicInteriorGradientSupConstant) *
            (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) * r := by
      intro x hx
      let D : ℝ := 6 * (1728 * harmonicInteriorGradientSupConstant) *
        (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) * r
      have hdiffint : Integrable (fun y => |H x - H y|)
          (volume.restrict Br) := by
        have hconst : Integrable (fun _ : Vec3 => H x)
            (volume.restrict Br) := integrableOn_const (μ := volume)
              (s := Br) hvol (by finiteness)
        simpa only [Pi.sub_apply, sub_eq_add_neg, Real.norm_eq_abs] using
          (hconst.sub hHint).norm
      have hdiffbound : ∀ᵐ y ∂volume.restrict Br, |H x - H y| ≤ D := by
        filter_upwards [ae_restrict_mem hBrmeas] with y hy
        have hLip := norm_sub_le_gradient_on_euclideanBall hr
          (hHdiff.mono hBrI) (fun z hz => hHgradSharp z (hBrI hz)) hx hy
        have hdiam := euclideanBall_pair_distance_le hr hx hy
        dsimp [D]
        calc
          |H x - H y| = |H y - H x| := abs_sub_comm _ _
          _ ≤ 3 * (1728 * harmonicInteriorGradientSupConstant *
              (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ ρ))) *
              vec3EuclideanNorm (y - x) := by
            exact hLip.trans_eq (by ring)
          _ ≤ 6 * (1728 * harmonicInteriorGradientSupConstant) *
              (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) * r := by
            calc
              3 * (1728 * harmonicInteriorGradientSupConstant *
                  (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                    (volume.restrict (euclideanBall x₀ ρ))) *
                  vec3EuclideanNorm (y - x) ≤
                  3 * (1728 * harmonicInteriorGradientSupConstant *
                    (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                      (volume.restrict (euclideanBall x₀ ρ))) * (2 * r) := by
                have hA : 0 ≤ 3 * (1728 * harmonicInteriorGradientSupConstant *
                    (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                      (volume.restrict (euclideanBall x₀ ρ))) := by
                  apply mul_nonneg (by norm_num)
                  apply mul_nonneg
                  · apply mul_nonneg
                    · exact mul_nonneg (by norm_num) hG
                    · exact inv_nonneg.mpr (by positivity)
                  · exact hL
                exact mul_le_mul_of_nonneg_left hdiam hA
              _ = 6 * (1728 * harmonicInteriorGradientSupConstant) *
                  (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                    (volume.restrict (euclideanBall x₀ ρ)) * r := by ring
      have hdiffconst : Integrable (fun _ : Vec3 => D)
          (volume.restrict Br) := integrableOn_const (μ := volume)
            (s := Br) hvol (by finiteness)
      have hdiffint' := integral_mono_ae hdiffint hdiffconst hdiffbound
      have hdiffint'' : (∫ y in Br, |H x - H y|) ≤
          (volume Br).toReal * D := by
        simpa [MeasureTheory.measureReal_def, smul_eq_mul] using hdiffint'
      have hraw := norm_sub_integralAverage_le_volumeAverage_integral_norm_sub
        (U := Br) hHint x hvolpos
      have hraw' : |H x - ⨍ y in Br, H y ∂volume| ≤
          (volume Br).toReal⁻¹ * (∫ y in Br, |H x - H y|) := by
        simpa only [CKN.integralAverage, Real.norm_eq_abs] using hraw
      calc
        |H x - ⨍ y in Br, H y ∂volume| ≤
            (volume Br).toReal⁻¹ * ((volume Br).toReal * D) :=
          hraw'.trans (mul_le_mul_of_nonneg_left hdiffint'' (by positivity))
        _ = D := by field_simp [ne_of_gt hvolpos]
        _ = 6 * (1728 * harmonicInteriorGradientSupConstant) *
            (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) * r := by rfl
    have havgeq : ⨍ y in Br, h y ∂volume = ⨍ y in Br, H y ∂volume := by
      rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
      rw [integral_congr_ae hEqBr]
    have hoscpoint : ∀ᵐ y ∂volume.restrict Br,
        |h y - ⨍ z in Br, h z ∂volume| ≤
          6 * (1728 * harmonicInteriorGradientSupConstant) *
            (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) * r := by
      filter_upwards [hEqBr, ae_restrict_mem hBrmeas] with y hyEq hy
      rw [hyEq, havgeq]
      exact hmean y hy
    have hmemosc : MemLp (fun y => h y - ⨍ z in Br, h z ∂volume)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict Br) := by
      let a : ℝ := ⨍ z in Br, h z ∂volume
      change MemLp (fun y => h y - a) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ r))
      have hh := hmemBr.sub (memLp_const a)
      convert hh using 1
    have hint := set_integral_rpow_bound hmemosc hvol hoscpoint
    have hbound := mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ (r ^ 2)⁻¹)
    have hoscC : (Real.pi * 4 / 3) *
        (6 * (1728 * harmonicInteriorGradientSupConstant)) ^
          (3 / 2 : ℝ) ≤ harmonicInteriorDisplayConstant := by
      dsimp [harmonicInteriorDisplayConstant]
      exact (le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    calc
      (r ^ 2)⁻¹ * ∫ y in Br,
          |h y - ⨍ z in Br, h z ∂volume| ^ (3 / 2 : ℝ) ≤
          (r ^ 2)⁻¹ * ((volume Br).toReal *
            (6 * (1728 * harmonicInteriorGradientSupConstant) *
              (ρ ^ 3)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ ρ)) * r) ^
              (3 / 2 : ℝ)) := hbound
      _ = ((Real.pi * 4 / 3) *
          (6 * (1728 * harmonicInteriorGradientSupConstant)) ^
            (3 / 2 : ℝ)) * (r / ρ) ^ (5 / 2 : ℝ) *
          (ρ ^ 2)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ)) ^ (3 / 2 : ℝ) := by
        rw [hvolreal]
        exact oscillation_display_scaling hr hρ
          (mul_nonneg (by norm_num) hG) hL
      _ ≤ harmonicInteriorDisplayConstant * (r / ρ) ^ (5 / 2 : ℝ) *
          (ρ ^ 2)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) ^ (3 / 2 : ℝ) := by
        gcongr
      _ = harmonicInteriorDisplayConstant * (r / ρ) ^ (5 / 2 : ℝ) *
          (ρ ^ 2)⁻¹ * ∫ y in euclideanBall x₀ ρ, |h y| ^ (3 / 2 : ℝ) := by
        rw [henergy]

  refine ⟨H, hHdiff, hHae, hHvalue, hHgrad, hplain, hosc⟩

end CKN.Foundation.Heat
