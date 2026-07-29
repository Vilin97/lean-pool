/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.CoordinateMeasure

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module MeasureTheory
open scoped RealInnerProductSpace

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An ambient fourier gaussian used in the Odlyzko-bound argument. -/
noncomputable def ambientFourierGaussian
    (a : ℝ) (w y : E) : ℂ :=
  Complex.exp
    (-(a : ℂ) * (‖y‖ : ℂ) ^ 2 +
      (-2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ w y : ℂ))

theorem integrable_ambientFourierGaussian
    {a : ℝ} (ha : 0 < a) (w : E) :
    Integrable (ambientFourierGaussian a w) := by
  have h :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (a : ℂ)) (by simp_all) (-2 * (Real.pi : ℂ) * Complex.I) w
  convert h using 1 with y
  unfold ambientFourierGaussian
  simp

omit [MeasurableSpace E] [BorelSpace E] in
theorem coordinateFourierGaussian_eq_ambient
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierGaussian L b a n x =
      ambientFourierGaussian a (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
  rw [coordinateFourierGaussian, coordinateFourierCharacter,
    mFourier_neg_torusQuotientMap]
  unfold coordinateGaussian latticeGaussian ambientFourierGaussian
  rw [← Complex.exp_add]
  rw [inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm L b n x]
  push_cast
  ring_nf

omit [DecidableEq ι] in
theorem integrable_coordinateFourierGaussian
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    Integrable (coordinateFourierGaussian L b a n) := by
  classical
  have h := integrable_comp_ofZLatticeBasis_equivFun_symm L b
    (integrable_ambientFourierGaussian
      (E := E) ha (dualLatticePoint L b n))
  apply h.congr
  filter_upwards with x
  exact (coordinateFourierGaussian_eq_ambient L b a n x).symm

theorem integral_ambientFourierGaussian
    {a : ℝ} (ha : 0 < a) (w : E) :
    (∫ y : E, ambientFourierGaussian a w y) =
      ((Real.pi : ℂ) / a) ^
          (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp
          (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / a) := by
  rw [← fourier_gaussian_innerProductSpace (b := (a : ℂ))
    (by simp_all) w]
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with y
  unfold ambientFourierGaussian
  rw [smul_eq_mul, ← Complex.exp_add]
  push_cast
  rw [real_inner_comm y w]
  ring_nf

theorem mFourierCoeff_gaussianTorusPeriodization_eq
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha) n =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          Complex.exp
            (-(Real.pi : ℂ) ^ 2 *
              (‖dualLatticePoint L b n‖ : ℂ) ^ 2 / a)) := by
  rw [mFourierCoeff_gaussianTorusPeriodization L b ha n
    (integrable_coordinateFourierGaussian L b ha n)]
  simp_rw [coordinateFourierGaussian_eq_ambient L b a n]
  rw [integral_comp_ofZLatticeBasis_equivFun_symm L b,
    integral_ambientFourierGaussian ha]

end NumberField.Odlyzko
