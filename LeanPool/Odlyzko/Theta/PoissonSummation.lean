/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.GaussianFourierCoefficient

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module MeasureTheory

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*}

theorem exp_fourierGaussian_eq_latticeGaussian
    {a : ℝ} (_ha : 0 < a) (w : E) :
    Complex.exp
        (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / a) =
      latticeGaussian (Real.pi ^ 2 / a) w := by
  unfold latticeGaussian
  push_cast
  grind

theorem summable_mFourierCoeff_gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [Fintype ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable
      (UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha)) := by
  classical
  have hp : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  have hdual :
      Summable (fun n : ι → ℤ ↦
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n)) := by
    have hs := (Equiv.summable_iff
      (e := (dualLatticeBasis L b).equivFun.toEquiv.symm)).mpr
        (summable_latticeGaussian (dualLattice L) hp)
    simpa [Function.comp_def, dualLatticePoint] using hs
  let C : ℂ :=
    (Real.toNNReal (ZLattice.covolume L))⁻¹ •
      (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ))
  have hscaled : Summable (fun n : ι → ℤ ↦
      C * latticeGaussian (Real.pi ^ 2 / a)
        (dualLatticePoint L b n)) :=
    hdual.mul_left C
  apply hscaled.congr
  intro n
  rw [mFourierCoeff_gaussianTorusPeriodization_eq L b ha n,
    exp_fourierGaussian_eq_latticeGaussian ha]
  dsimp [C]
  simp

theorem latticeGaussian_poissonSummation_of_basis
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [Finite ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    latticeTheta L a =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          dualLatticeTheta L (Real.pi ^ 2 / a)) := by
  classical
  letI := Fintype.ofFinite ι
  have hsummable :=
    summable_mFourierCoeff_gaussianTorusPeriodization L b ha
  have hseries :=
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      hsummable (0 : UnitAddTorus ι)
  have hsum :
      (∑' n : ι → ℤ,
          UnitAddTorus.mFourierCoeff
            (gaussianTorusPeriodization L b a ha) n) =
        gaussianTorusPeriodization L b a ha 0 := by
    rw [← hseries.tsum_eq]
    apply tsum_congr
    intro n
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one,
      smul_eq_mul, mul_one]
  rw [← gaussianTorusPeriodization_zero L b ha, ← hsum]
  simp_rw [mFourierCoeff_gaussianTorusPeriodization_eq L b ha,
    exp_fourierGaussian_eq_latticeGaussian ha]
  have hp : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  have hdual :
      Summable (fun n : ι → ℤ ↦
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n)) := by
    have hs := (Equiv.summable_iff
      (e := (dualLatticeBasis L b).equivFun.toEquiv.symm)).mpr
        (summable_latticeGaussian (dualLattice L) hp)
    simpa [Function.comp_def, dualLatticePoint] using hs
  have hinner := hdual.mul_left
    (((Real.pi : ℂ) / a) ^
      (Module.finrank ℝ E / 2 : ℂ))
  let c : NNReal :=
    (Real.toNNReal (ZLattice.covolume L volume))⁻¹
  change
    (∑' n : ι → ℤ,
      c • (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ) *
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n))) =
      c • (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ) *
        dualLatticeTheta L (Real.pi ^ 2 / a))
  rw [hinner.tsum_const_smul c]
  rw [tsum_mul_left]
  rw [← dualLatticeTheta_eq_tsum_coordinates L b]

theorem latticeGaussian_poissonSummation
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ℝ} (ha : 0 < a) :
    latticeTheta L a =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          dualLatticeTheta L (Real.pi ^ 2 / a)) := by
  let b := Free.chooseBasis ℤ L
  exact latticeGaussian_poissonSummation_of_basis L b ha

end NumberField.Odlyzko
