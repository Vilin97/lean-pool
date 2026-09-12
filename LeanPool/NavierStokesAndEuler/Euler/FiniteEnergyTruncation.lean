/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CompactParameterIntegral
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import LeanPool.NavierStokesAndEuler.ForMathlib.FiniteDimensionalBumps
public import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothCutoff
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
import LeanPool.NavierStokesAndEuler.Euler.RadialPotentialL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Divergence-free truncation by a radial vector potential

For a smooth divergence-free velocity `u`, the radial homotopy formula
produces a vector potential. Cutting off that potential and taking its curl
gives compact smooth divergence-free velocities that agree with `u` on any
prescribed ball. This construction does not assume Sobolev regularity of `u`.
-/

@[expose] public section

attribute [local instance] FiniteDimensional.hasContDiffBump


noncomputable section


open Set MeasureTheory Filter EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff Topology

namespace Euler.ComparatorBridge

/-- The coordinate potential `-x × u(x)`. -/
def negativeCrossPotential (u : Space → Space) (i : Fin 3) (x : Space) : ℝ :=
  x (i + 2) * u x (i + 1) - x (i + 1) * u x (i + 2)

theorem negativeCrossPotential_smooth (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (negativeCrossPotential u i) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff
  exact ((hc _).mul ((hc _).comp hu)).sub ((hc _).mul ((hc _).comp hu))

theorem partialDerivative_negativeCrossPotential
    (u : Space → Space) (hu : Differentiable ℝ u) (i j : Fin 3) (x : Space) :
    partialDerivative (negativeCrossPotential u i) j x =
      (EuclideanSpace.single j (1 : ℝ) : Space) (i + 2) * u x (i + 1) +
      x (i + 2) * (fderiv ℝ u x (EuclideanSpace.single j 1)) (i + 1) -
      ((EuclideanSpace.single j (1 : ℝ) : Space) (i + 1) * u x (i + 2) +
      x (i + 1) * (fderiv ℝ u x (EuclideanSpace.single j 1)) (i + 2)) := by
  have hc (a : Fin 3) := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x a
  have hv (a : Fin 3) :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (u x) a).comp x (hu x).hasFDerivAt
  have hd := ((hc (i + 2)).mul (hv (i + 1))).sub
    ((hc (i + 1)).mul (hv (i + 2)))
  change HasFDerivAt (negativeCrossPotential u i) _ x at hd
  rw [partialDerivative, hd.fderiv]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, smul_eq_mul, Function.comp_apply]
  ring

/-- The elementary curl identity behind the radial homotopy formula. -/
theorem curl_negativeCrossPotential
    (u : Space → Space) (hu : Differentiable ℝ u) (x : Space) :
    curl (negativeCrossPotential u) x =
      (2 : ℝ) • u x + fderiv ℝ u x x - divergence u x • x := by
  have hx : (∑ j : Fin 3, x j • (EuclideanSpace.single j 1 : Space)) = x := by
    simpa using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  have hd (i : Fin 3) : (fderiv ℝ u x x) i =
      ∑ j : Fin 3, x j * (fderiv ℝ u x (EuclideanSpace.single j 1)) i := by
    calc
      (fderiv ℝ u x x) i =
          (fderiv ℝ u x (∑ j : Fin 3, x j • EuclideanSpace.single j 1)) i := by rw [hx]
      _ = _ := by simp [map_sum, map_smul, smul_eq_mul]
  ext i
  fin_cases i <;>
    simp [curl_apply, partialDerivative_negativeCrossPotential u hu,
      divergence_eq_coordinate_sum, Fin.sum_univ_three, PiLp.sub_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hd] <;> ring

/-- The radial average whose negative cross product is a vector potential. -/
def radialAverage (u : Space → Space) (x : Space) : Space :=
  ∫ t in (0 : ℝ)..1, t • u (t • x)

/-- A smooth velocity gives a jointly smooth radial integrand. -/
theorem radialIntegrand_smooth (u : Space → Space) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun xt : Space × ℝ => xt.2 • u (xt.2 • xt.1)) :=
  contDiff_snd.smul (hu.comp (contDiff_snd.smul contDiff_fst))

theorem radialAverage_smooth (u : Space → Space) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (radialAverage u) :=
  EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) _
    (radialIntegrand_smooth u hu)

theorem radialIntegrand_parameterDerivative
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (x : Space) (t : ℝ) :
    EulerCompactParameterIntegral.parameterDerivative
      (fun xt : Space × ℝ => xt.2 • u (xt.2 • xt.1)) (x, t) =
      t ^ 2 • fderiv ℝ u (t • x) := by
  have hf := radialIntegrand_smooth u hu
  have hin : HasFDerivAt (fun y : Space => (y, t))
      (ContinuousLinearMap.inl ℝ Space ℝ) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) t x)
  have hpartial := ((hf.differentiable (by simp)) (x, t)).hasFDerivAt.comp x hin
  have hscaled := (((hu.differentiable (by simp)) (t • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul t)).const_smul t
  have he : t • ((fderiv ℝ u (t • x)).comp (t • ContinuousLinearMap.id ℝ Space)) =
      t ^ 2 • fderiv ℝ u (t • x) := by
    ext y
    simp [smul_smul, pow_two]
  rw [he] at hscaled
  exact hpartial.unique hscaled

theorem fderiv_radialAverage (u : Space → Space) (hu : ContDiff ℝ ∞ u) (x : Space) :
    fderiv ℝ (radialAverage u) x = ∫ t in (0 : ℝ)..1, t ^ 2 • fderiv ℝ u (t • x) := by
  have h := EulerCompactParameterIntegral.integral_hasFDerivAt 0 1 (by norm_num)
    (fun xt : Space × ℝ => xt.2 • u (xt.2 • xt.1)) (radialIntegrand_smooth u hu) x
  change HasFDerivAt (radialAverage u) _ x at h
  rw [h.fderiv]
  apply intervalIntegral.integral_congr
  intro t _
  exact radialIntegrand_parameterDerivative u hu x t

theorem radialDerivative_continuous (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (x : Space) : Continuous (fun t : ℝ => t ^ 2 • fderiv ℝ u (t • x)) :=
  (continuous_id.pow 2).smul
    ((hu.fderiv_right (m := ∞) (by simp)).continuous.comp
      (continuous_id.smul continuous_const))

theorem divergence_radialAverage (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (hdiv : ∀ x, divergence u x = 0) (x : Space) :
    divergence (radialAverage u) x = 0 := by
  rw [divergence, ← coordinateTrace_eq_linearTrace, fderiv_radialAverage u hu]
  rw [← coordinateTrace.intervalIntegral_comp_comm
    ((radialDerivative_continuous u hu x).intervalIntegrable 0 1)]
  have he : (fun t : ℝ => coordinateTrace (t ^ 2 • fderiv ℝ u (t • x))) = 0 := by
    funext t
    rw [map_smul, coordinateTrace_eq_linearTrace]
    change t ^ 2 • divergence u (t • x) = 0
    rw [hdiv, smul_zero]
  rw [he]
  exact intervalIntegral.integral_zero

/-- Differentiating `t² u(tx)` proves the radial homotopy identity. -/
theorem radialAverage_radial_identity
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (x : Space) :
    (2 : ℝ) • radialAverage u x + fderiv ℝ (radialAverage u) x x = u x := by
  have hv : Continuous (fun t : ℝ => t • u (t • x)) :=
    continuous_id.smul (hu.continuous.comp (continuous_id.smul continuous_const))
  have hd : Continuous (fun t : ℝ => (t ^ 2 • fderiv ℝ u (t • x)) x) :=
    (radialDerivative_continuous u hu x).clm_apply continuous_const
  have htime (t : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2 • u (r • x))
      ((2 * t) • u (t • x) + t ^ 2 • fderiv ℝ u (t • x) x) t := by
    have hspace := ((hu.differentiable (by simp)) (t • x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    convert! ((hasDerivAt_id t).pow 2).smul hspace using 1
    simp [Function.comp_apply, add_comm]
  have hv2 : Continuous (fun t : ℝ => (2 * t) • u (t • x)) := by
    fun_prop
  have hd2 : Continuous (fun t : ℝ => t ^ 2 • fderiv ℝ u (t • x) x) := by
    simpa only [smul_apply] using hd
  have hcont : Continuous (fun t : ℝ =>
      (2 * t) • u (t • x) + t ^ 2 • fderiv ℝ u (t • x) x) := by
    exact hv2.add hd2
  have ht : (∫ t in (0 : ℝ)..1,
      (2 * t) • u (t • x) + t ^ 2 • fderiv ℝ u (t • x) x) =
      (1 : ℝ) ^ 2 • u ((1 : ℝ) • x) - (0 : ℝ) ^ 2 • u ((0 : ℝ) • x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => htime t)
      (hcont.intervalIntegrable 0 1)
  have hi : (∫ t in (0 : ℝ)..1,
      (2 * t) • u (t • x) + t ^ 2 • fderiv ℝ u (t • x) x) =
      (2 : ℝ) • radialAverage u x + fderiv ℝ (radialAverage u) x x := by
    rw [intervalIntegral.integral_add (hv2.intervalIntegrable 0 1) (hd2.intervalIntegrable 0 1),
      fderiv_radialAverage u hu,
      ContinuousLinearMap.intervalIntegral_apply
        ((radialDerivative_continuous u hu x).intervalIntegrable 0 1)]
    congr 1
    change (∫ t in (0 : ℝ)..1, (2 * t) • u (t • x)) =
      (2 : ℝ) • (∫ t in (0 : ℝ)..1, t • u (t • x))
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _
    simp [smul_smul]
  rw [hi] at ht
  simpa using ht

/-- The concrete radial vector potential, in the development's curl convention. -/
def radialPotential (u : Space → Space) : Fin 3 → Space → ℝ :=
  negativeCrossPotential (radialAverage u)

theorem radialPotential_smooth (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (i : Fin 3) : ContDiff ℝ ∞ (radialPotential u i) :=
  negativeCrossPotential_smooth _ (radialAverage_smooth u hu) i

/-- The radial construction recovers every smooth divergence-free velocity. -/
theorem curl_radialPotential (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (hdiv : ∀ x, divergence u x = 0) (x : Space) :
    curl (radialPotential u) x = u x := by
  rw [radialPotential, curl_negativeCrossPotential _
    ((radialAverage_smooth u hu).differentiable (by simp)),
    divergence_radialAverage u hu hdiv, zero_smul, sub_zero]
  exact radialAverage_radial_identity u hu x

/-- Cut off the constructed potential, then take its actual curl. -/
def potentialTruncation (u : Space → Space) (χ : Space → ℝ) : Space → Space :=
  curl (fun i x => χ x * radialPotential u i x)

theorem potentialTruncation_smooth (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (potentialTruncation u χ) :=
  contDiff_curl _ (fun i => hχ.mul (radialPotential_smooth u hu i))

theorem potentialTruncation_divergence (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (x : Space) :
    divergence (potentialTruncation u χ) x = 0 :=
  divergence_curl _ (fun i => hχ.mul (radialPotential_smooth u hu i)) x

theorem potentialTruncation_support (u : Space → Space) (χ : Space → ℝ) :
    tsupport (potentialTruncation u χ) ⊆ tsupport χ :=
  tsupport_curl_subset _ _ (isClosed_tsupport χ)
    (fun _ => tsupport_mul_subset_left)

theorem potentialTruncation_compact (u : Space → Space) (χ : Space → ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (potentialTruncation u χ) :=
  hχ.of_isClosed_subset (isClosed_tsupport _) (potentialTruncation_support u χ)

theorem potentialTruncation_eq (u : Space → Space) (hu : ContDiff ℝ ∞ u)
    (hdiv : ∀ x, divergence u x = 0) (χ : Space → ℝ) (x : Space)
    (hχ : χ =ᶠ[𝓝 x] 1) : potentialTruncation u χ x = u x := by
  have he (i : Fin 3) : (fun y => χ y * radialPotential u i y) =ᶠ[𝓝 x]
      radialPotential u i := by
    filter_upwards [hχ] with y hy
    simp only [hy, Pi.one_apply, one_mul]
  exact (curl_congr_nhds _ _ x he).trans (curl_radialPotential u hu hdiv x)

/-- No all-order integrability is needed to construct compact solenoidal
extensions agreeing with a smooth divergence-free field on a ball. -/
theorem exists_compact_solenoidal_truncation
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, divergence u x = 0)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    ∃ w : Space → Space, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ Metric.closedBall 0 R ∧
      (∀ x, divergence w x = 0) ∧ (∀ x ∈ Metric.ball 0 r, w x = u x) := by
  let χ : ContDiffBump (0 : Space) := ⟨r, R, hr, hrR⟩
  refine ⟨potentialTruncation u χ, potentialTruncation_smooth u hu χ χ.contDiff,
    potentialTruncation_compact u χ χ.hasCompactSupport, ?_,
    potentialTruncation_divergence u hu χ χ.contDiff, ?_⟩
  · exact (potentialTruncation_support u χ).trans_eq χ.tsupport_eq
  · intro x hx
    exact potentialTruncation_eq u hu hdiv χ x (χ.eventuallyEq_one_of_mem_ball hx)

theorem partialDerivative_mul (f g : Space → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3) (x : Space) :
    partialDerivative (fun y => f y * g y) j x =
      f x * partialDerivative g j x + partialDerivative f j x * g x := by
  rw [partialDerivative, fderiv_fun_mul (hf x) (hg x)]
  simp [partialDerivative, mul_comm]

theorem curl_mul_apply (χ : Space → ℝ) (ψ : Fin 3 → Space → ℝ)
    (hχ : Differentiable ℝ χ) (hψ : ∀ i, Differentiable ℝ (ψ i))
    (x : Space) (i : Fin 3) :
    curl (fun j y => χ y * ψ j y) x i = χ x * curl ψ x i +
      partialDerivative χ (i + 1) x * ψ (i + 2) x -
      partialDerivative χ (i + 2) x * ψ (i + 1) x := by
  simp only [curl_apply, partialDerivative_mul χ _ hχ (hψ _)]
  ring

theorem norm_radialPotential_le (u : Space → Space) (i : Fin 3) (x : Space) :
    ‖radialPotential u i x‖ ≤ 2 * ‖x‖ * ‖radialAverage u x‖ := by
  have hprod (j k : Fin 3) : ‖x j * radialAverage u x k‖ ≤
      ‖x‖ * ‖radialAverage u x‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le x j) (PiLp.norm_apply_le (radialAverage u x) k)
      (norm_nonneg _) (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by
    dsimp only [radialPotential, negativeCrossPotential]
    nlinarith [hprod (i + 2) (i + 1), hprod (i + 1) (i + 2)])

/-- Cutting off the potential introduces only a zeroth-order error in the
radial average, with no derivative of the original velocity in the bound. -/
theorem potentialTruncation_error_bound
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, divergence u x = 0)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (x : Space) :
    ‖potentialTruncation u χ x - χ x • u x‖ ≤
      12 * ‖fderiv ℝ χ x‖ * ‖x‖ * ‖radialAverage u x‖ := by
  have hc (i : Fin 3) : ‖partialDerivative χ i x‖ ≤ ‖fderiv ℝ χ x‖ := by
    simpa [partialDerivative] using
      (fderiv ℝ χ x).le_opNorm (EuclideanSpace.single i 1)
  have he (i : Fin 3) : (potentialTruncation u χ x - χ x • u x) i =
      partialDerivative χ (i + 1) x * radialPotential u (i + 2) x -
      partialDerivative χ (i + 2) x * radialPotential u (i + 1) x := by
    simp only [potentialTruncation, curl_mul_apply χ _ (hχ.differentiable (by simp))
      (fun j => (radialPotential_smooth u hu j).differentiable (by simp)),
      curl_radialPotential u hu hdiv, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hp (i j : Fin 3) :
      ‖partialDerivative χ i x * radialPotential u j x‖ ≤
        ‖fderiv ℝ χ x‖ * (2 * ‖x‖ * ‖radialAverage u x‖) := by
    rw [norm_mul]
    exact mul_le_mul (hc i) (norm_radialPotential_le u j x) (norm_nonneg _) (norm_nonneg _)
  calc
    ‖potentialTruncation u χ x - χ x • u x‖ ≤
        ∑ i : Fin 3, ‖(potentialTruncation u χ x - χ x • u x) i‖ :=
      EulerMeanCutoffCurl.norm_le_sum_coordinates _
    _ ≤ ∑ _i : Fin 3, 4 * ‖fderiv ℝ χ x‖ * ‖x‖ * ‖radialAverage u x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [he]
      exact (norm_sub_le _ _).trans (by
        nlinarith [hp (i + 1) (i + 2), hp (i + 2) (i + 1)])
    _ = _ := by simp; ring

theorem potentialTruncation_norm_bound
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, divergence u x = 0)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (C : ℝ)
    (hχbound : ∀ x, ‖χ x‖ ≤ 1)
    (hderiv : ∀ x, ‖fderiv ℝ χ x‖ * ‖x‖ ≤ C) (x : Space) :
    ‖potentialTruncation u χ x‖ ≤ ‖u x‖ + 12 * C * ‖radialAverage u x‖ := by
  have herror := potentialTruncation_error_bound u hu hdiv χ hχ x
  have hmain : ‖χ x • u x‖ ≤ ‖u x‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hχbound x) (norm_nonneg _)).trans_eq (one_mul _)
  have hsplit := norm_le_norm_sub_add (potentialTruncation u χ x) (χ x • u x)
  have hscale := mul_le_mul_of_nonneg_right (hderiv x) (norm_nonneg (radialAverage u x))
  nlinarith

/-- A cutoff controlled in the scale-invariant derivative norm gives a
uniform finite-energy truncation. The numerical constant is inessential. -/
theorem potentialTruncation_energy_bound
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, divergence u x = 0)
    (huL2 : MemLp u 2 volume) (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχcompact : HasCompactSupport χ) (C : ℝ)
    (hχbound : ∀ x, ‖χ x‖ ≤ 1)
    (hderiv : ∀ x, ‖fderiv ℝ χ x‖ * ‖x‖ ≤ C) :
    MemLp (potentialTruncation u χ) 2 volume ∧
      (∫ x : Space, ‖potentialTruncation u χ x‖ ^ 2) ≤
        (2 + 1152 * C ^ 2) * (∫ x : Space, ‖u x‖ ^ 2) := by
  have hw : MemLp (potentialTruncation u χ) 2 volume :=
    (potentialTruncation_smooth u hu χ hχ).continuous.memLp_of_hasCompactSupport
      (potentialTruncation_compact u χ hχcompact)
  have hui : Integrable (fun x : Space => ‖u x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm huL2.aestronglyMeasurable).mp huL2
  have hwi : Integrable (fun x : Space => ‖potentialTruncation u χ x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  obtain ⟨hB, hBE⟩ := radial_average_memLp_and_energy u hu.continuous huL2
  change MemLp (radialAverage u) 2 volume at hB
  change (∫ x : Space, ‖radialAverage u x‖ ^ 2) ≤ 4 * (∫ x : Space, ‖u x‖ ^ 2) at hBE
  have hBi : Integrable (fun x : Space => ‖radialAverage u x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB
  have hp (x : Space) : ‖potentialTruncation u χ x‖ ^ 2 ≤
      2 * ‖u x‖ ^ 2 + 288 * C ^ 2 * ‖radialAverage u x‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (potentialTruncation_norm_bound
      u hu hdiv χ hχ C hχbound hderiv x) 2
    nlinarith [sq_nonneg (‖u x‖ - 12 * C * ‖radialAverage u x‖)]
  refine ⟨hw, ?_⟩
  calc
    (∫ x : Space, ‖potentialTruncation u χ x‖ ^ 2) ≤
        ∫ x : Space, 2 * ‖u x‖ ^ 2 + 288 * C ^ 2 * ‖radialAverage u x‖ ^ 2 :=
      integral_mono hwi ((hui.const_mul 2).add (hBi.const_mul (288 * C ^ 2))) hp
    _ = 2 * (∫ x : Space, ‖u x‖ ^ 2) +
        288 * C ^ 2 * (∫ x : Space, ‖radialAverage u x‖ ^ 2) := by
      rw [integral_add (hui.const_mul 2) (hBi.const_mul (288 * C ^ 2)),
        integral_const_mul, integral_const_mul]
    _ ≤ (2 + 1152 * C ^ 2) * (∫ x : Space, ‖u x‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hBE (by positivity : 0 ≤ 288 * C ^ 2)]

/-- A fixed bump is dilated, so its weighted derivative bound is independent
of the truncation radius. -/
def scaledCutoff (χ : Space → ℝ) (R : ℝ) (x : Space) : ℝ := χ (R⁻¹ • x)

theorem scaledCutoff_smooth (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) :
    ContDiff ℝ ∞ (scaledCutoff χ R) :=
  hχ.comp (contDiff_id.const_smul R⁻¹)

theorem scaledCutoff_compact (χ : Space → ℝ) (hχ : HasCompactSupport χ)
    (R : ℝ) (hR : R ≠ 0) : HasCompactSupport (scaledCutoff χ R) :=
  hχ.comp_smul (inv_ne_zero hR)

theorem scaledCutoff_derivative_position_bound
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (C : ℝ)
    (hC : ∀ x, ‖fderiv ℝ χ x‖ * ‖x‖ ≤ C) (R : ℝ) (x : Space) :
    ‖fderiv ℝ (scaledCutoff χ R) x‖ * ‖x‖ ≤ C := by
  have hd := ((hχ.differentiable (by simp)) (R⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul R⁻¹)
  have he : (fderiv ℝ χ (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space) =
      R⁻¹ • fderiv ℝ χ (R⁻¹ • x) := by
    ext y
    simp
  change HasFDerivAt (scaledCutoff χ R) _ x at hd
  rw [he] at hd
  rw [hd.fderiv, norm_smul]
  convert hC (R⁻¹ • x) using 1
  simp [norm_smul]
  ring

theorem exists_derivative_position_bound (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχcompact : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ χ x‖ * ‖x‖ ≤ C := by
  have hcompact : HasCompactSupport (fun x : Space => ‖fderiv ℝ χ x‖ * ‖x‖) :=
    (hχcompact.fderiv ℝ).norm.mul_right
  have hcont : Continuous (fun x : Space => ‖fderiv ℝ χ x‖ * ‖x‖) :=
    (hχ.fderiv_right (m := ∞) (by simp)).continuous.norm.mul continuous_norm
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  have hb (x : Space) : ‖fderiv ℝ χ x‖ * ‖x‖ ≤ C := by
    simpa only [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hC x
  exact ⟨C, by simpa using hb 0, hb⟩

/-- Unit truncation bump, given by `⟨1, 2, by norm_num, by norm_num⟩`. -/
def unitTruncationBump : ContDiffBump (0 : Space) :=
  NavierStokesAndEuler.SmoothCutoff.baseBump Space

/-- Truncation cutoff, given by `scaledCutoff unitTruncationBump R`. -/
def truncationCutoff (R : ℝ) : Space → ℝ :=
  NavierStokesAndEuler.SmoothCutoff.cutoff Space R

theorem truncationCutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (truncationCutoff R) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_smooth R

theorem truncationCutoff_norm_le (R : ℝ) (x : Space) : ‖truncationCutoff R x‖ ≤ 1 :=
  NavierStokesAndEuler.SmoothCutoff.norm_cutoff_le_one R x

theorem truncationCutoff_compact (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (truncationCutoff R) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_hasCompactSupport hR

theorem truncationCutoff_support (R : ℝ) (hR : 0 < R) :
    tsupport (truncationCutoff R) ⊆ Metric.closedBall 0 (2 * R) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_tsupport_subset hR

theorem truncationCutoff_eventually_one (R : ℝ) (hR : 0 < R) (x : Space)
    (hx : ‖x‖ < R) : truncationCutoff R =ᶠ[𝓝 x] 1 :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_eventuallyEq_one hR hx

/-- The truncation family used by the finite-energy flow argument. -/
def finiteEnergyTruncation (u : Space → Space) (R : ℝ) : Space → Space :=
  potentialTruncation u (truncationCutoff R)

theorem finiteEnergyTruncation_smooth
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (R : ℝ) :
    ContDiff ℝ ∞ (finiteEnergyTruncation u R) :=
  potentialTruncation_smooth u hu _ (truncationCutoff_smooth R)

theorem finiteEnergyTruncation_divergence
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (R : ℝ) (x : Space) :
    divergence (finiteEnergyTruncation u R) x = 0 :=
  potentialTruncation_divergence u hu _ (truncationCutoff_smooth R) x

theorem finiteEnergyTruncation_compact (u : Space → Space) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (finiteEnergyTruncation u R) :=
  potentialTruncation_compact u _ (truncationCutoff_compact R hR)

theorem finiteEnergyTruncation_support (u : Space → Space) (R : ℝ) (hR : 0 < R) :
    tsupport (finiteEnergyTruncation u R) ⊆ Metric.closedBall 0 (2 * R) :=
  (potentialTruncation_support u _).trans (truncationCutoff_support R hR)

theorem finiteEnergyTruncation_eq
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, divergence u x = 0)
    (R : ℝ) (hR : 0 < R) (x : Space) (hx : ‖x‖ < R) :
    finiteEnergyTruncation u R x = u x :=
  potentialTruncation_eq u hu hdiv _ x (truncationCutoff_eventually_one R hR x hx)

theorem unitTruncationBump_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (unitTruncationBump : Space → ℝ) x‖ * ‖x‖ ≤ C :=
  exists_derivative_position_bound _ unitTruncationBump.contDiff
      unitTruncationBump.hasCompactSupport

/-- A fixed finite constant independent of the velocity and cutoff radius. -/
def truncationEnergyConstant : ℝ := 2 + 1152 * unitTruncationBump_derivative_bound.choose ^ 2

theorem truncationEnergyConstant_nonneg : 0 ≤ truncationEnergyConstant := by
  unfold truncationEnergyConstant
  positivity

/-- The concrete compact solenoidal truncations have uniformly controlled
energy, using only the original velocity's finite energy and smoothness. -/
theorem finiteEnergyTruncation_energy_bound
    (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, divergence u x = 0)
    (huL2 : MemLp u 2 volume) (R : ℝ) (hR : 0 < R) :
    MemLp (finiteEnergyTruncation u R) 2 volume ∧
      (∫ x : Space, ‖finiteEnergyTruncation u R x‖ ^ 2) ≤
        truncationEnergyConstant * (∫ x : Space, ‖u x‖ ^ 2) := by
  apply potentialTruncation_energy_bound u hu hdiv huL2 _ (truncationCutoff_smooth R)
    (truncationCutoff_compact R hR) unitTruncationBump_derivative_bound.choose
    (truncationCutoff_norm_le R)
  exact scaledCutoff_derivative_position_bound unitTruncationBump
    unitTruncationBump.contDiff _ unitTruncationBump_derivative_bound.choose_spec.2 R

end Euler.ComparatorBridge
