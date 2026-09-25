/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness

/-!
# Conversions

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-- The square of `alpha` is its normalized time-slice energy. -/
theorem alpha_sq_eq (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ)
    (hr : 0 < r) :
    alpha u z r ^ 2 = r⁻¹ *
      (timeSliceEnergyEssSup z.1 z.2 r
        (fun w => vec3EuclideanNorm (u w))).toReal := by
  rw [alpha, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity

/-- The square of `beta` is its normalized gradient integral. -/
theorem beta_sq_eq (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (r : ℝ) (hr : 0 < r) :
    beta u Du z r ^ 2 = r⁻¹ *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (spatialGradientSq u Du w)).toReal := by
  rw [beta, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity

/-- The cube of `gamma` is its normalized velocity integral. -/
theorem gamma_cube_eq (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ)
    (hr : 0 < r) :
    gamma u z r ^ 3 = r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
  rw [gamma, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity

/-- The cube of `delta` is its normalized pressure integral. -/
theorem delta_cube_eq (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ)
    (hr : 0 < r) :
    delta p z r ^ 3 = r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := by
  rw [delta, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity

/-- The `q`-power of `lambda` separates its radius factor and force integral. -/
theorem lambda_pow_eq (q : ℝ) (f : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (r : ℝ) (hr : 0 < r) (hq : 0 < q) :
    lambda q f z r ^ q =
      (r ^ (3 - 5 / q)) ^ q *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal := by
  rw [lambda]
  have hJ : 0 ≤
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal :=
    ENNReal.toReal_nonneg
  have hJpow :
      ((∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1 / q : ℝ)) ^ q =
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal := by
    rw [← Real.rpow_mul hJ]
    have hq' : (1 / q) * q = (1 : ℝ) := by field_simp
    rw [hq', Real.rpow_one]
  calc
    (r ^ (3 - 5 / q) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1 / q : ℝ)) ^ q =
        (r ^ (3 - 5 / q)) ^ q *
          ((∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^
              (1 / q : ℝ)) ^ q :=
      Real.mul_rpow (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hJ _)
    _ = _ := by rw [hJpow]

/-- A nonnegative Bochner set integral is the real form of its `ofReal` lintegral. -/
theorem setIntegral_eq_toReal_setLIntegral_of_nonneg
    {α : Type*} [MeasureSpace α] {s : Set α} {g : α → ℝ}
    (hg : IntegrableOn g s volume) (hgn : 0 ≤ᵐ[volume.restrict s] g) :
    ∫ x in s, g x =
      (∫⁻ x in s, ENNReal.ofReal (g x)).toReal := by
  have hnon : 0 ≤ ∫ x in s, g x := integral_nonneg_of_ae hgn
  rw [← ENNReal.toReal_ofReal hnon]
  rw [ofReal_integral_eq_lintegral_ofReal hg hgn]

end CKN
