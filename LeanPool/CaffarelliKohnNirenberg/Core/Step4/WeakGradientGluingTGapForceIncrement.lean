/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTInstanceInteriorCollar
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotHarmonic

/-! # The force increment on an interior pressure collar

The difference of the two classical gradients is the gradient of the
annular force potential. Its coefficient is uniform for collars of radius
at least one over 128, without an additive data-independent remainder.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

/-- The force-potential increment in the actual pressure decomposition. -/
@[expose]
def gapForceIncrement (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (i : Fin 3) (w : ParabolicPoint) : ℝ :=
  let η := mollifiedBallCutoff z.1 hρ
  let c := sourceSliceCentredMean z.1 ρ u
  classicalGradient (harmonicPressurePart η u c p w.2 + pressureP8 η f w.2) w.1 i -
    classicalGradient (harmonicPressurePart η u c p w.2) w.1 i

/-- An absolute coefficient for the force increment on either half-gap collar. -/
def gapForceIncrementCoefficient : ℝ :=
  400 * sliceForcePotentialConstant * cutoffGradientConstant * (128 : ℝ)^3

/-- The absolute force-increment coefficient is nonnegative. -/
theorem gapForceIncrementCoefficient_nonneg : 0 ≤ gapForceIncrementCoefficient := by
  unfold gapForceIncrementCoefficient
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) sliceForcePotentialConstant_nonneg)
    cutoffGradientConstant_nonneg_global) (by norm_num)

/-- Suitability identifies the force increment with the annular force
potential's derivative on almost every slice of the half-collar. -/
theorem gap_force_increment_eq_pressureP8_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2), ∀ i : Fin 3,
      ∀ x ∈ vec3Ball z.1 (ρ/2), gapForceIncrement z hρ u p f i (x,s) =
        classicalGradient (pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i := by
  have hh := slice_harmonic_part_contDiffOn_ae_of_sws (z := z) hsol hρ hsub
  have hf := slice_force_source_data_ae_of_sws (z := z) hsol hρ hsub
  have hhalf := CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
    (x₀ := z.1) (by positivity : 0 < ρ/2)
  filter_upwards [hh,hf] with s hs hfs
  rw [hhalf] at hs
  intro i x hx
  have hd₁ := hs.differentiableOn_one.differentiableAt ((isOpen_vec3Ball _ _).mem_nhds hx)
  have hd₂ := (contDiffOn_pressureP8_halfBall hρ hfs.2.2.1).differentiableOn_one.differentiableAt
    ((isOpen_vec3Ball _ _).mem_nhds hx)
  have he := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i))
    (hd₁.hasFDerivAt.add hd₂.hasFDerivAt).fderiv
  change classicalGradient _ x i = classicalGradient _ x i + classicalGradient _ x i at he
  exact sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))

/-- The force increment is bounded by the slice force mass, uniformly for
collar radii at least one over 128. -/
theorem gap_force_increment_majorant_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ) (hlo : 1 / 128 ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2), ∀ i : Fin 3,
      ∀ x ∈ vec3Ball z.1 (ρ/2), ‖gapForceIncrement z hρ u p f i (x,s)‖ₑ ≤
        ENNReal.ofReal gapForceIncrementCoefficient *
          ∫⁻ y in vec3Ball z.1 ρ, ENNReal.ofReal (vec3EuclideanNorm (f (y,s))) := by
  have hi := gap_force_increment_eq_pressureP8_ae_of_sws hsol hρ hsub
  have hf := slice_force_source_data_ae_of_sws (z := z) hsol hρ hsub
  have hc : 0 ≤ 400 * sliceForcePotentialConstant * cutoffGradientConstant :=
    mul_nonneg (mul_nonneg (by norm_num) sliceForcePotentialConstant_nonneg)
      cutoffGradientConstant_nonneg_global
  have hinv : ρ⁻¹ ≤ 128 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/128) hlo
    norm_num only [one_div, inv_div, div_one] at h
    exact h
  filter_upwards [hi,hf] with s his hfs
  intro i x hx
  rw [his i x hx, Real.enorm_eq_ofReal_abs]
  have hF : 0 ≤ ∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (f (y,s)) :=
    integral_nonneg (fun _ => vec3EuclideanNorm_nonneg _)
  have hA : 0 ≤ (cutoffGradientConstant/ρ) * ∫ y in vec3Ball z.1 ρ,
      vec3EuclideanNorm (f (y,s)) := mul_nonneg
        (div_nonneg cutoffGradientConstant_nonneg_global hρ.le) hF
  have hb := (abs_apply_le_vec3EuclideanNorm _ i).trans
    (vec3EuclideanNorm_classicalGradient_pressureP8_le hρ hA hfs.2.2.1 hfs.2.2.2 hx)
  have heq : 400 * sliceForcePotentialConstant *
      ((cutoffGradientConstant/ρ) * ∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (f (y,s))) *
      (ρ^2)⁻¹ = (400 * sliceForcePotentialConstant * cutoffGradientConstant) * (ρ⁻¹)^3 *
        ∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (f (y,s)) := by
    rw [div_eq_mul_inv, inv_pow]
    ring
  rw [heq] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) hinv 3) hc) hF)
  have he := ENNReal.ofReal_le_ofReal hb'
  change _ ≤ ENNReal.ofReal (gapForceIncrementCoefficient *
    ∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (f (y,s))) at he
  rw [ENNReal.ofReal_mul gapForceIncrementCoefficient_nonneg] at he
  rw [ofReal_integral_eq_lintegral_ofReal hfs.1
    (Filter.Eventually.of_forall (fun _ => vec3EuclideanNorm_nonneg _))] at he
  exact he

end CKN.Core.Step4
