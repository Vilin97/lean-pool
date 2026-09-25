/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-!
# Uniform force-source Morrey bounds

A scalar source supported on the unit cylinder and dominated there by the
force inherits its global integral bound. The global Lebesgue-to-Morrey
estimate and unit-support exponent reduction preserve a fully numerical
bound, with no conversion of infinite integrals to real numbers.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- The force-source bound determined by the unit-cylinder data size. -/
def forceSourceMorreyBound (q ε₀ : ℝ) : ℝ≥0∞ :=
  volume (parabolicCylinder (0 : Vec3) 0 1) ^ (5 / 6 - 1 / q : ℝ) *
    ENNReal.ofReal ε₀ ^ (1 / q : ℝ)

/-- The numerical force-source bound is finite in the admissible force range. -/
theorem forceSourceMorreyBound_lt_top (q ε₀ : ℝ) (hq : 5 / 2 < q) :
    forceSourceMorreyBound q ε₀ < ⊤ := by
  have hq0 : 0 < q := by linarith only [hq]
  have hqP : (6 / 5 : ℝ) ≤ q := by linarith only [hq]
  have hexp : 0 ≤ (5 / 6 - 1 / q : ℝ) := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6 / 5) hqP
    norm_num at hi
    simpa only [one_div] using sub_nonneg.mpr hi
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hexp Integration.volume_parabolicCylinder_lt_top.ne)
    (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hq0.le) ENNReal.ofReal_ne_top)

/-- The original small-data sum controls the global force-source integral
when the source vanishes outside the unit cylinder and is dominated inside. -/
theorem force_source_integral_le_of_small_data
    (q ε₀ : ℝ) (hq : 0 < q)
    {u f : ParabolicPoint → Vec3} {p F : ParabolicPoint → ℝ}
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hdom : ∀ᵐ z ∂volume.restrict (parabolicCylinder (0 : Vec3) 0 1),
      |F z| ≤ vec3EuclideanNorm (f z))
    (hsupp : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 1, F z = 0) :
    (∫⁻ z, ENNReal.ofReal |F z| ^ q) ≤ ENNReal.ofReal ε₀ := by
  have hsupport : Function.support (fun z => ENNReal.ofReal |F z| ^ q) ⊆
      parabolicCylinder (0 : Vec3) 0 1 := by
    intro z hz
    by_contra hnot
    apply hz
    simp only [hsupp z hnot, abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq]
  rw [← setLIntegral_eq_of_support_subset hsupport]
  calc
    _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q :=
      lintegral_mono_ae (hdom.mono (fun z hz =>
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hz) hq.le))
    _ ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q :=
      lintegral_mono (fun _ => le_add_left le_rfl)
    _ ≤ _ := hsmall

/-- The force-source Morrey estimate at the original force exponent. -/
theorem force_source_morrey_le_of_small_data
    (q ε₀ : ℝ) (hq : 5 / 2 < q)
    {u f : ParabolicPoint → Vec3} {p F : ParabolicPoint → ℝ}
    (hF : AEMeasurable F volume)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hdom : ∀ᵐ z ∂volume.restrict (parabolicCylinder (0 : Vec3) 0 1),
      |F z| ≤ vec3EuclideanNorm (f z))
    (hsupp : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 1, F z = 0) :
    morreyNorm (6 / 5 : ℝ) q F ≤ forceSourceMorreyBound q ε₀ := by
  have hq0 : 0 < q := by linarith only [hq]
  have hint := force_source_integral_le_of_small_data q ε₀ hq0 hsmall hdom hsupp
  have hLp : eLpNorm' F q volume ≤ ENNReal.ofReal ε₀ ^ (1 / q : ℝ) := by
    rw [eLpNorm'_eq_lintegral_enorm]
    simp only [Real.enorm_eq_ofReal_abs]
    exact ENNReal.rpow_le_rpow hint (one_div_nonneg.mpr hq0.le)
  have hm := morreyNorm_le_eLpNorm' (p := (6 / 5 : ℝ)) (q := q)
    (by norm_num) (by linarith only [hq]) hF
  have hexp : (1 / (6 / 5) : ℝ) = 5 / 6 := by norm_num
  rw [hexp] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hLp (by positivity))

/-- On unit support, the paper heat-source exponent is reached without
increasing the numerical bound. -/
theorem force_source_paper_morrey_le_of_small_data
    (q ε₀ : ℝ) (hq : 5 / 2 < q)
    {u f : ParabolicPoint → Vec3} {p F : ParabolicPoint → ℝ}
    (hF : AEMeasurable F volume)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hdom : ∀ᵐ z ∂volume.restrict (parabolicCylinder (0 : Vec3) 0 1),
      |F z| ≤ vec3EuclideanNorm (f z))
    (hsupp : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 1, F z = 0) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ)) F ≤ forceSourceMorreyBound q ε₀ := by
  have hPq : (6 / 5 : ℝ) ≤ q := by linarith only [hq]
  have hlower := morreyNorm_lower_morrey_exponent (p := (6 / 5 : ℝ)) (q := q)
    (q' := min q (25 / 9 : ℝ)) (by norm_num) hPq
    (le_min hPq (by norm_num)) (min_le_left _ _) (z₀ := ((0, 0) : ParabolicPoint))
    one_pos hsupp
  simp only [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] at hlower
  exact hlower.trans (force_source_morrey_le_of_small_data q ε₀ hq hF hsmall hdom hsupp)

end CKN.Core.Endgame
