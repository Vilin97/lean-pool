/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Complex.SubMean
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Existence for the Dirichlet problem on a disk

For continuous boundary data `f` on the circle `sphere c R`, the Schwarz
integral

  `schwarzIntegral f c R w = ⨍ z, herglotzRieszKernel c w z * f z`

is holomorphic in `w` on `ball c R`; its real part is the Poisson integral of
`f`, which tends to `f ζ₀` as `w → ζ₀ ∈ sphere c R` (positive kernel, unit
mass, approximate identity). Together: `exists_harmonic_extension`, the
solution of the Dirichlet problem (Anghel–Stan "Poisson integral formula";
Rainer/Forster Theorem 22.3; Hubbard's use in §1.2).

Mathlib anchors (pinned commit `905b9581`):
* `herglotzRieszKernel`, `poissonKernel`, `poissonKernel_eq_re_herglotzRieszKernel`,
  `re_herglotzRieszKernel_le`, `le_re_herglotzRieszKernel`
  (`Mathlib/Analysis/Complex/Poisson.lean`); conventions: in
  `poissonKernel c w z`, `w` is the interior point, `z` the circle variable.
* `DiffContOnCl.circleAverage_poissonKernel_smul`: for `f` holomorphic on the
  ball and continuous up to the closure, `⨍ z, poissonKernel c w z • f z = f w`
  — applied to `f = 1` this gives the unit-mass identity.
* `Real.circleAverage` API (`Mathlib/MeasureTheory/Integral/CircleAverage.lean`),
  `circleMap`, `intervalIntegral` differentiation under the integral
  (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
* `AnalyticAt.harmonicAt_re`, `InnerProductSpace.HarmonicAt`
  (`Mathlib/Analysis/InnerProductSpace/Harmonic/`,
  `Mathlib/Analysis/Complex/Harmonic/`).
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex Real

namespace Rado

/-- The Schwarz integral of boundary data `f` on `sphere c R`, evaluated at the
interior point `w`. -/
noncomputable def schwarzIntegral (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  Real.circleAverage (fun z ↦ herglotzRieszKernel c w z * (f z : ℂ)) c R

section Kernel

variable {c w z : ℂ} {R : ℝ}

/-- For `w` inside the ball and `z` on the bounding sphere, `z ≠ w` (stated in
the subtracted form in which the kernel denominators appear). -/
private theorem sub_sub_ne_zero (hw : w ∈ ball c R) (hz : z ∈ sphere c R) :
    (z - c) - (w - c) ≠ 0 := by
  have hz' : ‖z - c‖ = R := mem_sphere_iff_norm.1 hz
  have hw' : ‖w - c‖ < R := mem_ball_iff_norm.1 hw
  intro h
  rw [sub_eq_zero] at h
  rw [h] at hz'
  exact hw'.ne hz'

/-- Positivity of the Poisson kernel for interior `w`, boundary `z`. -/
theorem poissonKernel_pos (hw : w ∈ ball c R) (hz : z ∈ sphere c R) :
    0 < poissonKernel c w z := by
  have hz' : ‖z - c‖ = R := mem_sphere_iff_norm.1 hz
  have hw' : ‖w - c‖ < R := mem_ball_iff_norm.1 hw
  rw [poissonKernel_def]
  apply div_pos
  · rw [hz']
    have h0 : (0 : ℝ) ≤ ‖w - c‖ := norm_nonneg _
    nlinarith
  · exact pow_pos (norm_pos_iff.mpr (sub_sub_ne_zero hw hz)) 2

/-- The Poisson kernel is continuous on the circle, for a fixed interior
point. -/
private theorem continuousOn_poissonKernel (hw : w ∈ ball c R) :
    ContinuousOn (poissonKernel c w) (sphere c R) := by
  intro z hz
  have hne : ‖(z - c) - (w - c)‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_sub_ne_zero hw hz))
  have h : ContinuousAt
      (fun z : ℂ ↦ (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2) z :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hne
  exact h.continuousWithinAt

/-- Unit mass of the Poisson kernel. -/
theorem circleAverage_poissonKernel (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w) c R = 1 := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hint : CircleIntegrable (poissonKernel c w) c R :=
    (continuousOn_poissonKernel hw).circleIntegrable hR.le
  have hconst : DiffContOnCl ℂ (fun _ : ℂ ↦ (1 : ℂ)) (ball c R) :=
    ⟨differentiableOn_const _, continuousOn_const⟩
  have h1 := hconst.circleAverage_poissonKernel_smul hw
  have h2 : (poissonKernel c w • fun _ : ℂ ↦ (1 : ℂ))
      = fun z ↦ ((poissonKernel c w z : ℝ) : ℂ) := by
    ext z
    simp [Pi.smul_apply', Complex.real_smul]
  have h3 := Complex.ofRealCLM.circleAverage_comp_comm hint
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h3
  have h4 : ((Real.circleAverage (poissonKernel c w) c R : ℝ) : ℂ) = 1 := by
    rw [← h3, ← h2]
    exact h1
  exact_mod_cast h4

/-- Uniform smallness of the Poisson kernel away from the boundary singularity:
for `z` at distance `≥ δ` from `ζ₀ ∈ sphere c R`, the kernel at `z` becomes
uniformly `≤ ε` as the interior point `w` approaches `ζ₀`. -/
theorem eventually_poissonKernel_le_of_dist {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere c R) (hR : 0 < R)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝[ball c R] ζ₀, ∀ z ∈ sphere c R, δ ≤ dist z ζ₀ → poissonKernel c w z ≤ ε := by
  have hη : (0 : ℝ) < min (δ / 2) (ε * (δ / 2) ^ 2 / (2 * R)) :=
    lt_min (by positivity) (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds ζ₀ hη)] with w hw hwη z hz hzδ
  have hwζ : dist w ζ₀ < min (δ / 2) (ε * (δ / 2) ^ 2 / (2 * R)) := mem_ball.1 hwη
  have hwζ₁ : dist w ζ₀ < δ / 2 := hwζ.trans_le (min_le_left _ _)
  have hwζ₂ : dist w ζ₀ < ε * (δ / 2) ^ 2 / (2 * R) := hwζ.trans_le (min_le_right _ _)
  have hwc : ‖w - c‖ < R := mem_ball_iff_norm.1 hw
  have hzc : ‖z - c‖ = R := mem_sphere_iff_norm.1 hz
  have hζc : ‖ζ₀ - c‖ = R := mem_sphere_iff_norm.1 hζ₀
  have hd0 : (0 : ℝ) ≤ dist w ζ₀ := dist_nonneg
  -- lower bound for the denominator
  have hzw : δ / 2 ≤ ‖(z - c) - (w - c)‖ := by
    have h1 : (z - c) - (w - c) = z - w := by ring
    rw [h1, ← dist_eq_norm]
    have h2 := dist_triangle z w ζ₀
    linarith
  have hden : (0 : ℝ) < ‖(z - c) - (w - c)‖ ^ 2 :=
    pow_pos (lt_of_lt_of_le (by positivity) hzw) 2
  -- upper bound for the numerator
  have hnum : ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2 ≤ 2 * R * dist w ζ₀ := by
    have h1 : R - ‖w - c‖ ≤ dist w ζ₀ := by
      have h2 := norm_sub_norm_le (ζ₀ - c) (w - c)
      have h3 : (ζ₀ - c) - (w - c) = ζ₀ - w := by ring
      rw [h3, hζc] at h2
      rw [dist_comm, dist_eq_norm]
      exact h2
    have h4 : (0 : ℝ) ≤ ‖w - c‖ := norm_nonneg _
    rw [hzc]
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ R + ‖w - c‖),
      mul_le_mul_of_nonneg_left (le_of_lt hwc) hd0]
  rw [poissonKernel_def, div_le_iff₀ hden]
  calc ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2
      ≤ 2 * R * dist w ζ₀ := hnum
    _ ≤ 2 * R * (ε * (δ / 2) ^ 2 / (2 * R)) :=
        mul_le_mul_of_nonneg_left hwζ₂.le (by positivity)
    _ = ε * (δ / 2) ^ 2 := by
        have h2R : (2 : ℝ) * R ≠ 0 := by positivity
        field_simp
    _ ≤ ε * ‖(z - c) - (w - c)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hzw 2) hε.le

end Kernel

section Schwarz

variable {f : ℂ → ℝ} {c : ℂ} {R : ℝ}

/-- Real circle averages commute with multiplication by a constant. -/
private theorem circleAverage_const_mul (a : ℝ) (g : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    Real.circleAverage (fun z ↦ a * g z) c R = a * Real.circleAverage g c R := by
  simpa [smul_eq_mul] using
    Real.circleAverage_fun_smul (a := a) (f := g) (c := c) (R := R)

/-- Complex circle averages commute with multiplication by a constant. -/
private theorem circleAverage_const_mul_complex (a : ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    Real.circleAverage (fun z ↦ a * g z) c R = a * Real.circleAverage g c R := by
  simpa [smul_eq_mul] using
    Real.circleAverage_fun_smul (a := a) (f := g) (c := c) (R := R)

/-- The Schwarz integrand is continuous on the circle, for a fixed interior
point. -/
private theorem continuousOn_kernel_mul {w : ℂ} (hw : w ∈ ball c R)
    (hf : ContinuousOn f (sphere c R)) :
    ContinuousOn (fun z ↦ herglotzRieszKernel c w z * (f z : ℂ)) (sphere c R) := by
  have hg : ContinuousOn (fun z ↦ ((f z : ℝ) : ℂ)) (sphere c R) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  simp only [herglotzRieszKernel_def]
  apply ContinuousOn.mul _ hg
  intro z hz
  have h : ContinuousAt (fun z : ℂ ↦ ((z - c) + (w - c)) / ((z - c) - (w - c))) z :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (sub_sub_ne_zero hw hz)
  exact h.continuousWithinAt

/-- The Schwarz integral is holomorphic in the interior variable
(differentiation under the integral). -/
theorem schwarzIntegral_differentiableOn (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    DifferentiableOn ℂ (schwarzIntegral f c R) (ball c R) := by
  have hg : ContinuousOn (fun z ↦ ((f z : ℝ) : ℂ)) (sphere c R) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hgint : CircleIntegrable (fun z ↦ ((f z : ℝ) : ℂ)) c R := hg.circleIntegrable hR.le
  -- the Cauchy-type integral is differentiable on the ball
  have hR0 : 0 < R.toNNReal := Real.toNNReal_pos.2 hR
  have hcoe : (R.toNNReal : ℝ) = R := Real.coe_toNNReal R hR.le
  have hgint' : CircleIntegrable (fun z ↦ ((f z : ℝ) : ℂ)) c R.toNNReal := by rwa [hcoe]
  have hdiff : DifferentiableOn ℂ
      (fun w ↦ (2 * (π : ℂ) * I)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • ((f z : ℝ) : ℂ))
      (ball c R) := by
    have h := (hasFPowerSeriesOn_cauchy_integral hgint' hR0).differentiableOn
    rwa [Metric.eball_coe, hcoe] at h
  have hRHS : DifferentiableOn ℂ
      (fun w ↦ (2 : ℂ) * ((2 * (π : ℂ) * I)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • ((f z : ℝ) : ℂ))
        - Real.circleAverage (fun z ↦ ((f z : ℝ) : ℂ)) c R) (ball c R) :=
    (hdiff.const_mul 2).sub_const _
  apply hRHS.congr
  intro w hw
  have hwz : ∀ z ∈ sphere c R, z - w ≠ 0 := by
    intro z hz
    have h := sub_sub_ne_zero hw hz
    rwa [sub_sub_sub_cancel_right] at h
  have hA_cont : ContinuousOn (fun z ↦ (z - c) / (z - w) * ((f z : ℝ) : ℂ)) (sphere c R) := by
    apply ContinuousOn.mul _ hg
    intro z hz
    have h : ContinuousAt (fun z : ℂ ↦ (z - c) / (z - w)) z :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (hwz z hz)
    exact h.continuousWithinAt
  have hA_int : CircleIntegrable (fun z ↦ (z - c) / (z - w) * ((f z : ℝ) : ℂ)) c R :=
    hA_cont.circleIntegrable hR.le
  have hA2_int : CircleIntegrable
      (fun z ↦ (2 : ℂ) * ((z - c) / (z - w) * ((f z : ℝ) : ℂ))) c R :=
    (continuousOn_const.mul hA_cont).circleIntegrable hR.le
  calc schwarzIntegral f c R w
      = Real.circleAverage (fun z ↦ herglotzRieszKernel c w z * ((f z : ℝ) : ℂ)) c R := rfl
    _ = Real.circleAverage
          (fun z ↦ 2 * ((z - c) / (z - w) * ((f z : ℝ) : ℂ)) - ((f z : ℝ) : ℂ)) c R := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        rw [abs_of_pos hR] at hz
        have h1 : z - w ≠ 0 := hwz z hz
        have h2 : (z - c) - (w - c) = z - w := sub_sub_sub_cancel_right z w c
        simp only [herglotzRieszKernel_def, h2]
        field_simp
        try ring
    _ = Real.circleAverage (fun z ↦ (2 : ℂ) * ((z - c) / (z - w) * ((f z : ℝ) : ℂ))) c R
        - Real.circleAverage (fun z ↦ ((f z : ℝ) : ℂ)) c R :=
        Real.circleAverage_fun_sub hA2_int hgint
    _ = 2 * Real.circleAverage (fun z ↦ (z - c) / (z - w) * ((f z : ℝ) : ℂ)) c R
        - Real.circleAverage (fun z ↦ ((f z : ℝ) : ℂ)) c R := by
        rw [circleAverage_const_mul_complex]
    _ = (2 : ℂ) * ((2 * (π : ℂ) * I)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • ((f z : ℝ) : ℂ))
        - Real.circleAverage (fun z ↦ ((f z : ℝ) : ℂ)) c R := by
        congr 2
        rw [Real.circleAverage_eq_circleIntegral hR.ne']
        congr 1
        apply circleIntegral.integral_congr hR.le
        intro z hz
        have h1 : z - w ≠ 0 := hwz z hz
        have h3 : z - c ≠ 0 := by
          rw [sub_ne_zero]
          intro h
          rw [mem_sphere_iff_norm, h, sub_self, norm_zero] at hz
          exact hR.ne' hz.symm
        simp only [smul_eq_mul]
        field_simp

/-- The real part of the Schwarz integral is the Poisson integral. -/
theorem re_schwarzIntegral {w : ℂ} (hR : 0 < R) (hf : ContinuousOn f (sphere c R))
    (hw : w ∈ ball c R) :
    (schwarzIntegral f c R w).re
      = Real.circleAverage (fun z ↦ poissonKernel c w z • f z) c R := by
  have hint : CircleIntegrable (fun z ↦ herglotzRieszKernel c w z * ((f z : ℝ) : ℂ)) c R :=
    (continuousOn_kernel_mul hw hf).circleIntegrable hR.le
  have h := Complex.reCLM.circleAverage_comp_comm hint
  simp only [Function.comp_def, Complex.reCLM_apply] at h
  change (Real.circleAverage (fun z ↦ herglotzRieszKernel c w z * ((f z : ℝ) : ℂ)) c R).re = _
  rw [← h]
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [abs_of_pos hR] at hz
  have hpk : poissonKernel c w z = (herglotzRieszKernel c w z).re :=
    congrFun poissonKernel_eq_re_herglotzRieszKernel z
  simp only [smul_eq_mul, hpk]
  simp [Complex.mul_re]

/-- Boundary attainment: the Poisson integral of continuous boundary data tends
to the data at each boundary point (approximate-identity argument, using
positivity, unit mass and off-singularity smallness of the kernel). -/
theorem tendsto_re_schwarzIntegral (hR : 0 < R) (hf : ContinuousOn f (sphere c R))
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere c R) :
    Filter.Tendsto (fun w ↦ (schwarzIntegral f c R w).re) (𝓝[ball c R] ζ₀) (𝓝 (f ζ₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hf
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM ζ₀ hζ₀)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousWithinAt_iff.1 (hf ζ₀ hζ₀) (ε / 4) (by positivity)
  have hε'' : (0 : ℝ) < ε / (4 * (M + 1)) := by positivity
  filter_upwards [self_mem_nhdsWithin,
    eventually_poissonKernel_le_of_dist hζ₀ hR hδ0 hε''] with w hw hfar
  rw [Real.dist_eq, re_schwarzIntegral hR hf hw]
  simp only [smul_eq_mul]
  -- integrability of all integrands in sight
  have hKcont : ContinuousOn (poissonKernel c w) (sphere c R) := continuousOn_poissonKernel hw
  have hKf_int : CircleIntegrable (fun z ↦ poissonKernel c w z * (f z - f ζ₀)) c R :=
    (hKcont.mul (hf.sub continuousOn_const)).circleIntegrable hR.le
  have hKf₁_int : CircleIntegrable (fun z ↦ poissonKernel c w z * f z) c R :=
    (hKcont.mul hf).circleIntegrable hR.le
  have hKf₂_int : CircleIntegrable (fun z ↦ poissonKernel c w z * f ζ₀) c R :=
    (hKcont.mul continuousOn_const).circleIntegrable hR.le
  have hbnd_int : CircleIntegrable
      (fun z ↦ ε / 4 * poissonKernel c w z + ε / (4 * (M + 1)) * (2 * M)) c R :=
    ((continuousOn_const.mul hKcont).add continuousOn_const).circleIntegrable hR.le
  have hunit : Real.circleAverage (poissonKernel c w) c R = 1 := circleAverage_poissonKernel hw
  -- the difference is the average of `K · (f - f ζ₀)`
  have key : Real.circleAverage (fun z ↦ poissonKernel c w z * f z) c R - f ζ₀
      = Real.circleAverage (fun z ↦ poissonKernel c w z * (f z - f ζ₀)) c R := by
    have h1 : Real.circleAverage (fun z ↦ poissonKernel c w z * (f z - f ζ₀)) c R
        = Real.circleAverage (fun z ↦ poissonKernel c w z * f z) c R
          - Real.circleAverage (fun z ↦ poissonKernel c w z * f ζ₀) c R := by
      calc Real.circleAverage (fun z ↦ poissonKernel c w z * (f z - f ζ₀)) c R
          = Real.circleAverage
              (fun z ↦ poissonKernel c w z * f z - poissonKernel c w z * f ζ₀) c R := by
            congr 1
            funext z
            ring
        _ = _ := Real.circleAverage_fun_sub hKf₁_int hKf₂_int
    rw [h1]
    have h2 : (fun z ↦ poissonKernel c w z * f ζ₀)
        = fun z ↦ f ζ₀ * poissonKernel c w z := by
      funext z
      ring
    rw [h2, circleAverage_const_mul, hunit, mul_one]
  rw [key]
  -- pointwise bound on the circle
  have hbound : ∀ z ∈ sphere c R,
      |poissonKernel c w z * (f z - f ζ₀)|
        ≤ ε / 4 * poissonKernel c w z + ε / (4 * (M + 1)) * (2 * M) := by
    intro z hz
    have hK0 : 0 < poissonKernel c w z := poissonKernel_pos hw hz
    rw [abs_mul, abs_of_pos hK0]
    rcases lt_or_ge (dist z ζ₀) δ with hnear | hfar'
    · -- near the singularity: `f` is close to `f ζ₀`
      have h1 : |f z - f ζ₀| ≤ ε / 4 := by
        have h := hδ hz hnear
        rw [Real.dist_eq] at h
        exact h.le
      have h2 : poissonKernel c w z * |f z - f ζ₀| ≤ poissonKernel c w z * (ε / 4) :=
        mul_le_mul_of_nonneg_left h1 hK0.le
      have h3 : (0 : ℝ) ≤ ε / (4 * (M + 1)) * (2 * M) := by positivity
      linarith
    · -- away from the singularity: the kernel is small
      have h1 : poissonKernel c w z ≤ ε / (4 * (M + 1)) := hfar z hz hfar'
      have h2 : |f z - f ζ₀| ≤ 2 * M := by
        calc |f z - f ζ₀| ≤ |f z| + |f ζ₀| := abs_sub _ _
          _ ≤ M + M := add_le_add (hM z hz) (hM ζ₀ hζ₀)
          _ = 2 * M := by ring
      have h3 : (0 : ℝ) ≤ ε / 4 * poissonKernel c w z :=
        mul_nonneg (by positivity) hK0.le
      have h4 : poissonKernel c w z * |f z - f ζ₀| ≤ ε / (4 * (M + 1)) * (2 * M) :=
        mul_le_mul h1 h2 (abs_nonneg _) hε''.le
      linarith
  -- integrate the bound
  calc |Real.circleAverage (fun z ↦ poissonKernel c w z * (f z - f ζ₀)) c R|
      ≤ Real.circleAverage |fun z ↦ poissonKernel c w z * (f z - f ζ₀)| c R :=
        Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage
          (fun z ↦ ε / 4 * poissonKernel c w z + ε / (4 * (M + 1)) * (2 * M)) c R := by
        apply Real.circleAverage_mono hKf_int.abs hbnd_int
        intro x hx
        rw [abs_of_pos hR] at hx
        simpa using hbound x hx
    _ = ε / 4 + ε / (4 * (M + 1)) * (2 * M) := by
        calc Real.circleAverage
              (fun z ↦ ε / 4 * poissonKernel c w z + ε / (4 * (M + 1)) * (2 * M)) c R
            = Real.circleAverage (fun z ↦ ε / 4 * poissonKernel c w z) c R
              + Real.circleAverage (fun _ ↦ ε / (4 * (M + 1)) * (2 * M)) c R :=
              Real.circleAverage_fun_add
                ((continuousOn_const.mul hKcont).circleIntegrable hR.le)
                (circleIntegrable_const _ _ _)
          _ = ε / 4 + ε / (4 * (M + 1)) * (2 * M) := by
              rw [circleAverage_const_mul, hunit, mul_one, Real.circleAverage_const]
    _ < ε := by
        have h1 : ε / (4 * (M + 1)) * (2 * M) ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
        linarith

end Schwarz

/-- **Solution of the Dirichlet problem on a disk.** Every continuous function
on a circle extends to a function continuous on the closed disk and harmonic
inside. -/
theorem exists_harmonic_extension {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere c R)) :
    ∃ u : ℂ → ℝ, ContinuousOn u (closedBall c R) ∧
      HarmonicOnNhd u (ball c R) ∧ EqOn u f (sphere c R) := by
  classical
  have hSdiff : DifferentiableOn ℂ (schwarzIntegral f c R) (ball c R) :=
    schwarzIntegral_differentiableOn hR hf
  refine ⟨fun w ↦ if w ∈ ball c R then (schwarzIntegral f c R w).re else f w, ?_, ?_, ?_⟩
  · -- continuity on the closed ball
    intro x hx
    rcases lt_or_eq_of_le (mem_closedBall.1 hx) with hlt | heq2
    · -- interior point
      have hxball : x ∈ ball c R := mem_ball.2 hlt
      have hS_cont : ContinuousAt (fun w ↦ (schwarzIntegral f c R w).re) x :=
        Complex.continuous_re.continuousAt.comp
          (hSdiff.analyticAt (isOpen_ball.mem_nhds hxball)).continuousAt
      have heqv : (fun w ↦ (schwarzIntegral f c R w).re) =ᶠ[𝓝 x]
          (fun w ↦ if w ∈ ball c R then (schwarzIntegral f c R w).re else f w) := by
        filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
        rw [ite_eq_left hy]
      exact (hS_cont.congr heqv).continuousWithinAt
    · -- boundary point
      have hxsph : x ∈ sphere c R := mem_sphere.2 heq2
      have hxnb : x ∉ ball c R := by
        rw [mem_ball, heq2]
        exact lt_irrefl R
      rw [← ball_union_sphere]
      apply ContinuousWithinAt.union
      · -- approach from the interior: boundary attainment
        have h1 := tendsto_re_schwarzIntegral hR hf hxsph
        have heqv : (fun w ↦ (schwarzIntegral f c R w).re) =ᶠ[𝓝[ball c R] x]
            (fun w ↦ if w ∈ ball c R then (schwarzIntegral f c R w).re else f w) := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          rw [ite_eq_left hy]
        have h2 := h1.congr' heqv
        change Filter.Tendsto
          (fun w ↦ if w ∈ ball c R then (schwarzIntegral f c R w).re else f w)
          (𝓝[ball c R] x)
          (𝓝 (if x ∈ ball c R then (schwarzIntegral f c R x).re else f x))
        rw [ite_eq_right hxnb]
        exact h2
      · -- approach along the sphere: the function agrees with `f` there
        apply (hf x hxsph).congr
        · intro y hy
          have hynb : y ∉ ball c R := by
            rw [mem_ball]
            rw [mem_sphere] at hy
            rw [hy]
            exact lt_irrefl R
          exact ite_eq_right hynb
        · exact ite_eq_right hxnb
  · -- harmonicity on the open ball
    intro x hx
    have hxan : AnalyticAt ℂ (schwarzIntegral f c R) x :=
      hSdiff.analyticAt (isOpen_ball.mem_nhds hx)
    have heqv : (fun w ↦ if w ∈ ball c R then (schwarzIntegral f c R w).re else f w)
        =ᶠ[𝓝 x] (fun w ↦ (schwarzIntegral f c R w).re) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact ite_eq_left hy
    exact (harmonicAt_congr_nhds heqv).2 hxan.harmonicAt_re
  · -- boundary values
    intro z hz
    have hznb : z ∉ ball c R := by
      rw [mem_ball]
      rw [mem_sphere] at hz
      rw [hz]
      exact lt_irrefl R
    exact ite_eq_right hznb

end Rado
