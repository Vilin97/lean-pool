/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.WeakPressureSlice
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-! # Slice-selected pressure gradients: classical, additive, quantitative forms

Display (3.5) of the pressure-gradient section selects, on a half ball, the
coordinate weak derivative of the pressure obtained by splitting it into a
particular potential and a smooth harmonic representative.  The ingredients
recorded here are exactly the ones that selection step consumes: a `C¹`
function has its classical coordinate gradient as a weak partial derivative,
weak partial derivatives add along an a.e. decomposition of the carrier, and a
coordinate field obeying a pointwise gradient display is controlled in `L^(6/5)`
on the half ball. -/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

private lemma euclideanBall_measurable_slice (x₀ : Vec3) (r : ℝ) :
    MeasurableSet (euclideanBall x₀ r) := by
  change MeasurableSet {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
  exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
    continuous_const).measurableSet

private lemma euclideanBall_eq_vec3Ball_slice {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- classical gradient of a C¹ function is its weak partial derivative -/
theorem hasWeakPartialDerivOn_classicalGradient
    {B : Set Vec3} (hB : IsOpen B) {h : Vec3 → ℝ} (k : Fin 3)
    (hh : ContDiffOn ℝ (1 : ℕ∞) h B) :
    HasWeakPartialDerivOn B k h (fun x => classicalGradient h x k) := by
  simpa only [classicalGradient_apply] using
    pressure_hasWeakPartialDerivOn_of_contDiffOn hB hh

/-- The classical coordinate gradient of a `C¹` function is locally
integrable, as required by display (3.5). -/
theorem locallyIntegrableOn_classicalGradient
    {B : Set Vec3} (hB : IsOpen B) {h : Vec3 → ℝ} (k : Fin 3)
    (hh : ContDiffOn ℝ (1 : ℕ∞) h B) :
    LocallyIntegrableOn (fun x => classicalGradient h x k) B volume := by
  have hHd : ContinuousOn (fun x => (fderiv ℝ h x) (basisVec k)) B :=
    (hh.continuousOn_fderiv_of_isOpen hB (by simp)).clm_apply continuousOn_const
  simpa only [classicalGradient_apply] using
    hHd.locallyIntegrableOn hB.measurableSet

/-- Display (3.5) decomposes the selected pressure into a particular and a
harmonic part; the weak partial derivatives of the two parts add. -/
theorem hasWeakPartialDerivOn_add
    {B : Set Vec3} (hB : IsOpen B) {k : Fin 3} {h w gh gw : Vec3 → ℝ}
    (hh : HasWeakPartialDerivOn B k h gh) (hw : HasWeakPartialDerivOn B k w gw)
    (hhloc : LocallyIntegrableOn h B volume) (hwloc : LocallyIntegrableOn w B volume)
    (hghloc : LocallyIntegrableOn gh B volume) (hgwloc : LocallyIntegrableOn gw B volume) :
    HasWeakPartialDerivOn B k (fun x => h x + w x) (fun x => gh x + gw x) :=
  CKN.Core.Endgame.weak_partial_deriv_of_ae_sum (B := B) hB
    (p := fun x => h x + w x) (P := h) (H := w) (gp := gh) (gh := gw) (k := k)
    (hrep := Filter.EventuallyEq.rfl) hh hw hhloc hwloc hghloc hgwloc

/-- the L^(6/5) bound on the half ball produced by a pointwise gradient display -/
theorem eLpNorm_classicalGradient_component_le_of_sup
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (k : Fin 3)
    (hmeas : AEStronglyMeasurable (fun x => classicalGradient h x k)
      (volume.restrict (euclideanBall x₀ (ρ / 2))))
    (hsup : ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm (classicalGradient h x) ≤ M) :
    eLpNorm (fun x => classicalGradient h x k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
      ENNReal.ofReal M * (volume (euclideanBall x₀ (ρ / 2))) ^ (5 / 6 : ℝ) := by
  let B : Set Vec3 := euclideanBall x₀ (ρ / 2)
  let μ : Measure Vec3 := volume.restrict B
  have hBmeas : MeasurableSet B := by
    dsimp only [B]
    exact euclideanBall_measurable_slice x₀ (ρ / 2)
  have hmemae : ∀ᵐ x ∂μ, x ∈ B := by
    simpa only [μ] using ae_restrict_mem hBmeas
  have hbound : ∀ᵐ x ∂μ, ‖classicalGradient h x k‖ ≤ M := by
    filter_upwards [hmemae] with x hx
    have hspace : ‖classicalGradient h x‖ ≤ vec3EuclideanNorm (classicalGradient h x) := by
      simpa only [spaceEuclideanNorm, vec3EuclideanNorm] using
        space_norm_le_euclideanNorm (classicalGradient h x)
    exact (norm_le_pi_norm (classicalGradient h x) k).trans
      (hspace.trans (hsup x (by simpa only [B] using hx)))
  have hμB : μ Set.univ = volume B := by
    simp only [μ, Measure.restrict_apply_univ]
  have hconst : eLpNorm (fun _ : Vec3 => M) (ENNReal.ofReal (6 / 5 : ℝ)) μ =
      ENNReal.ofReal M * (volume B) ^ (5 / 6 : ℝ) := by
    rw [eLpNorm_const M (by norm_num)]
    · rw [hμB]
      have hnorm : ‖M‖ₑ = ENNReal.ofReal M := by
        calc
          ‖M‖ₑ = ENNReal.ofReal ‖M‖ := (ofReal_norm M).symm
          _ = ENNReal.ofReal M := by rw [Real.norm_eq_abs, abs_of_nonneg hM]
      have hexp : (1 / (6 / 5 : ℝ)) = 5 / 6 := by norm_num
      rw [hnorm, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5), hexp]
    · intro hzero
      have hvol : volume B = 0 := by
        rw [← hμB, hzero]
        simp
      rw [show B = vec3Ball x₀ (ρ / 2) by
        dsimp only [B]
        exact euclideanBall_eq_vec3Ball_slice (by positivity)] at hvol
      rw [volume_vec3Ball_eq] at hvol
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ρ / 2) ^ 3 *
          ENNReal.ofReal (Real.pi * 4 / 3) := by positivity
      exact hpos.ne' hvol
  have hmono := eLpNorm_mono_ae_real (p := ENNReal.ofReal (6 / 5 : ℝ))
    (g := fun _ : Vec3 => M) (by simpa only [μ, B] using hmeas) hbound
  rw [hconst] at hmono
  simpa only [μ, B] using hmono

end CKN.Core.Step4
